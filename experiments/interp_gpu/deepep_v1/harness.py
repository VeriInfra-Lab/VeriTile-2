"""Per-rank harness of the `deepep-v1-intranode-001` batch: layout, dispatch and combine of the DeepEP version 1 port.

The port is TileScale at `9ba8a605`, `examples/distributed/deepseek_deepep/`.
Nothing of it is copied here: the harness imports it from the checkout that
the environment `tilescale-deepep` was built from (`gpurun.dist.deepep_port`)
and calls it through its own `EPBuffer`, in the order of its own test
(`intranode/example_intranode.py`). It changes no kernel and has not run on
the development host, which has no GPU.

Inputs, the same tensors in every rank; rank r owns slice r:

    x              bf16   [ranks, tokens, hidden]
    topk_idx       int64  [ranks, tokens, topk]    expert of each selection, -1 for none
    topk_weights   fp32   [ranks, tokens, topk]

`launch`: `num_experts`, and `scale`, one factor per rank. Between dispatch
and combine rank d returns every received row times `scale[d]`: the expert
step of the frozen `moeCombine_of_moeDispatch` with the weight of a token on
rank d equal to `scale[d]`.

Outputs of a rank. The dispatch results have room for `ranks * tokens` rows;
the rows a rank did not receive keep the sentinel.

    is_token_in_rank, num_tokens_per_rank, num_tokens_per_expert     layout
    recv_x, recv_src_idx, recv_topk_idx, recv_topk_weights           dispatch
    combined_x, combined_topk_weights                                combine

`judge.py` computes what each of them must hold.
"""
from dataclasses import replace
import os
from pathlib import Path
import sys


def run(rank, ranks, inputs, outputs, launch):
    from gpurun import dist
    return run_port(dist.deepep_port(), rank, ranks, inputs, outputs, launch)


def make_buffer(buffer_class, group, num_topk, hidden, launch):
    args = (group, 2**30, num_topk, launch['num_experts'], hidden)
    if 'ring' not in launch:
        return buffer_class(*args)
    # EPBuffer allocates with its own SM count. Both kernel configs must agree with it.
    from deepep_utils import Config
    ring = launch['ring']
    config = dict(num_sms=ring['num_sms'], num_max_nvl_chunked_recv_tokens=ring['recv_tokens'])
    dispatch = replace(Config.get_dispatch_config(group.size()), **config)
    combine = replace(Config.get_combine_config(group.size()),
                      num_max_nvl_chunked_send_tokens=ring['combine_send_tokens'], **config)
    # gpurun creates a fresh process per rank, so this class-level setting is local to this run.
    buffer_class.set_num_sms(ring['num_sms'])
    buf = buffer_class(*args, dispatch_cfg=dispatch, combine_cfg=combine)
    def sizes(cfg):
        return f'{cfg.num_max_nvl_chunked_send_tokens}/{cfg.num_max_nvl_chunked_recv_tokens}'

    sys.stdout.write(f'deepep-ring rank={group.rank()} channels={buf.num_channels} '
                     f'dispatch={sizes(buf.dispatch_cfg)} combine={sizes(buf.combine_cfg)}\n')
    sys.stdout.flush()
    return buf


def run_port(port, rank, ranks, inputs, outputs, launch, *, verify_origin=False):
    import torch
    sys.path.insert(0, str(port))  # the port's files import each other as top-level modules
    from buffer import EPBuffer
    if verify_origin:
        for name in ('buffer', 'deepep_utils', 'intranode.get_dispatch_layout', 'intranode.dispatch', 'intranode.combine'):
            expected = Path(port, *name.split('.')).with_suffix('.py').resolve()
            if Path(sys.modules[name].__file__).resolve() != expected:
                raise ValueError(f'{name} was imported outside the selected variant')
    from tilelang.distributed.utils import init_dist

    # init_dist reads WORLD_SIZE and RANK as the node count and this node's rank; the launcher set them per rank.
    per_rank = {name: os.environ.pop(name) for name in ('RANK', 'WORLD_SIZE')}
    try:
        _, _, group = init_dist(rank, ranks)  # process group over TCP, this rank on GPU `rank`
    finally:
        os.environ.update(per_rank)
    if (group.rank(), group.size()) != (rank, ranks):
        raise ValueError(f'the process group says rank {group.rank()} of {group.size()}; gpurun started {rank} of {ranks}')

    def keep(values):
        torch.cuda.synchronize()  # the port launches on a stream of its own and does not always wait for it
        for name, value in values.items():
            outputs[name][:value.shape[0]].copy_(value)
        # The log survives a later hang, the outputs do not.
        print(f'rank {rank}:', {name: tuple(value.shape) for name, value in values.items()}, flush=True)
        group.barrier()  # as the port's test does after each step

    # A clone is an allocation of its own, as the inputs of the port's test are.
    x, topk_idx, topk_weights = (inputs[name][rank].clone() for name in ('x', 'topk_idx', 'topk_weights'))
    buffer = make_buffer(EPBuffer, group, topk_idx.shape[1], x.shape[1], launch)

    num_tokens_per_rank, num_tokens_per_expert, is_token_in_rank = buffer.get_dispatch_layout(topk_idx)
    keep({'num_tokens_per_rank': num_tokens_per_rank, 'num_tokens_per_expert': num_tokens_per_expert,
          'is_token_in_rank': is_token_in_rank})
    print(f'rank {rank}: layout', num_tokens_per_rank.tolist(), num_tokens_per_expert.tolist(), flush=True)

    recv_x, recv_topk_idx, recv_topk_weights, _, handle = buffer.dispatch(
        x, None, num_tokens_per_rank, is_token_in_rank, num_tokens_per_expert, topk_idx, topk_weights, 1)
    keep({'recv_x': recv_x, 'recv_src_idx': handle[3], 'recv_topk_idx': recv_topk_idx,
          'recv_topk_weights': recv_topk_weights})

    returned = recv_x * launch['scale'][rank]
    torch.cuda.synchronize()  # complete before the combine reads it from the port's stream
    combined_x, combined_topk_weights = buffer.combine(returned, handle, recv_topk_weights)
    keep({'combined_x': combined_x, 'combined_topk_weights': combined_topk_weights})
    torch.distributed.destroy_process_group()
