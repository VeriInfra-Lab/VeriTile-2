[English](GpuInterNodeRuns.md) | [中文](GpuInterNodeRuns.zh.md)

# Single-host coverage of inter-node programs

Issue: [#353](https://github.com/VeriInfra-Lab/VeriTile-2/issues/353). Inspection date: 2026-11-10; logical-node launcher added on 2026-11-12; first logical-node result and the requests for tutorials 03 and 06 recorded on 2026-11-12; their results and the two requests with four GPUs recorded on 2026-11-13. Status: source inspection complete. The launcher that starts two logical nodes on the one host has run on the GPU side: `internode-logical-env-002` returned on 2026-11-12 and was judged pass (two logical nodes come up and a put between them lands). The requests for tutorials 03 and 06, `internode-logical-ag03-001` and `internode-logical-rs06-001`, ran on 2026-11-12 with two logical nodes of one rank and were judged pass on 2026-11-13. Of the two outcomes the issue allows, the first will not hold (decision below). The second, a recorded check that the inter-node code paths run on the one host, holds for the launch, for one put and for the `nnodes > 1` branches of tutorials 03 and 06 that one rank per logical node reaches. With two ranks per logical node, tutorial 03 passed (#466). Tutorial 06 passed on 2026-11-24 with the global NVSHMEM barrier. [Four-rank verdict](https://github.com/VeriInfra-Lab/VeriTile-2/issues/511#issuecomment-7124128151).

**Decision (user, 2026-11-12).** No second physical node will be arranged: the collaborator's cluster is no longer available. Inter-node programs are tested only as logical nodes on the one host. Transport between hosts (network cards, RDMA) is outside the scope of the project: the model has ranks and scopes, not nodes or links, so a proof does not depend on it. If logical nodes cannot be made to run, the inter-node code paths are proved and reported as not run.

## Hardware and scope

The inspected host exposes six H800 PCIe GPUs, all compute capability 9.0. NVLink pairs are 0–1, 2–3 and 4–5. Only two GPUs are intended for each distributed request, with one exception: the two requests `internode-logical-ag03-2x2-001` and `internode-logical-rs06-2x2-002` use four, two NVLink pairs (user decision, 2026-11-13). Two pairs are connected to each other over PCIe only. The local environment checks used the then-idle 4–5 pair. A device selection is not a resource reservation and occupancy must be rechecked before a run. The user granted a batch-specific exception on 2026-11-24 for the four-rank tutorial 06 run to share devices 0, 1, 2 and 3 with other workloads. The run measured correctness only.

All source observations below refer to [Triton-distributed `7908e4ea9010bb2238f9f05b28c904fd4b71c60a`](https://github.com/ByteDance-Seed/Triton-distributed/tree/7908e4ea9010bb2238f9f05b28c904fd4b71c60a). They establish control-flow and configuration constraints, not successful execution or numerical correctness.

Ordinary one-host/two-process launch gives `WORLD_SIZE=2`, `LOCAL_WORLD_SIZE=2`, and `NNODES=1`. A program named `inter_node` can then execute a reduced single-node path while skipping the inter-node communication it was written to exercise.

## Source findings

| Program | One-host/two-GPU source assessment | Missing coverage or blocker |
| --- | --- | --- |
| [Tutorial 03](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py) | Its 1D all-gather sends to the other rank through NVSHMEM. Its 2D all-gather accepts `NNODES=1` and uses the intra-node peer branch. Runtime is untested. | The 2D same-local-rank/different-node send and its receive/forward ordering are not covered when `NNODES=1`. |
| [Tutorial 03a](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03a-inter-node-allgather.py) | Not an NVIDIA tutorial at this pin: it imports `pyrocshmem`, uses ROCSHMEM device contexts and ROCSHMEM signal operations. | Cannot run unchanged in the H800/CUDA environment. An AMD/ROCm host or a separately reviewed NVIDIA port is needed. No port was made. |
| [Tutorial 06](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/06-inter-node-reduce-scatter.py) | The code explicitly supports `nnodes == 1`, returning the local reduce-scatter buffer. Runtime is untested. | `kernel_inter_node_p2p_for_same_local_rank` is launched only under `nnodes > 1`; a normal two-rank single-host run does not execute it. |
| [All-to-all inter-node kernel](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset_inter_node.py) | The core context can describe `world_size=2, local_world_size=2`. The supplied test calls `create_context` without overriding its default `local_world_size=8`. | The supplied two-rank test configuration violates `world_size % local_world_size == 0`. A dev-side adapter must explicitly pass 2. With one logical node, the different-node receive-wait branch is skipped. No test or kernel was edited. |
| [Sequence-parallel all-gather attention inter-node kernel](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/sp_ag_attention_inter_node.py) | Its test derives `NNODES` from `WORLD_SIZE / LOCAL_WORLD_SIZE` and passes both into the context. A two-rank single-host configuration follows its intra-node all-gather path. Runtime is untested. | Remote-node puts and cross-node receive/forward synchronization are not covered with `NNODES=1`. |

## Launch constraints

The pinned `scripts/launch.sh` recognizes `--nproc_per_node=2` (with `=`). Its fallback counts physical devices with `nvidia-smi`, so setting only `CUDA_VISIBLE_DEVICES` is insufficient on this six-GPU host. An eventual dev-side request must explicitly select two visible GPUs and two processes.

Do not falsify topology by changing only `LOCAL_WORLD_SIZE`: initialization maps `LOCAL_RANK` to the CUDA device, and symmetric peer-buffer construction also depends on the local grouping. A two-logical-node run on one physical host needs an explicit launcher and batch description; the next section describes them. Even when it executes remote-node source branches, it does not establish inter-host NIC, RDMA/IBGDA, isolation, latency or failure behavior.

## Logical nodes on the one host

Added on 2026-11-12. Of this section, the launcher and one put between two logical nodes have run on a GPU (`internode-logical-env-002`, subsection "First request and its result"); the later tutorial runs are recorded below. The launcher is also tested on the development host, which has no GPU, against a stand-in for the pinned script. Every statement about torchrun, NVSHMEM or NCCL is read in the cited source or inferred from it, and says which; the subsection "What only a run on the GPU side can settle" says which of them that run has since confirmed.

### Launcher

`gpurun` has a second `dist` launcher, `triton-dist-logical-nodes`, with the test field `logical_nodes` ([GpuExchangeProtocol.md](GpuExchangeProtocol.md), sections 5, 6 and 9). It starts the pinned `scripts/launch.sh` once per logical node, all on the one host, and drives it through the multi-node variables the script already reads. For `ranks` 2 and `logical_nodes` 2:

| Given to logical node n (0 or 1) | What the pinned script does with it (read in `scripts/launch.sh` at the pin) |
| --- | --- |
| `ARNOLD_WORKER_NUM=2`, `ARNOLD_ID=n` | Passes `--nnodes=2 --node_rank=n` to torchrun. |
| `--nproc_per_node=1` | One rank per node. Without the argument the script counts physical GPUs with `nvidia-smi`. |
| `ARNOLD_WORKER_0_HOST=127.0.0.1` | Passes `--rdzv_endpoint=127.0.0.1:<port>`. The address is a constant of the launcher. The port stays the script's: `23456`, or the operator's `ARNOLD_WORKER_0_PORT`. |
| `CUDA_VISIBLE_DEVICES=` the n-th entry of the operator's list | Not read by the script; inherited by torchrun and by the rank. |

Everything else stays as the script sets it, the NVSHMEM settings among them: `NVSHMEM_BOOTSTRAP=UID`, the bootstrap interface, the symmetric heap size, `NVSHMEM_DISABLE_CUDA_VMM=1`. The launcher needs no interface name: both logical nodes are on the host whose interface the operator already chose for `dist` batches. A request names no host, interface or address.

What each rank is then expected to see, by the torchrun source of the PyTorch version the GPU side reported (2.8.0; `torch/distributed/elastic/agent/server/local_elastic_agent.py`, and `_assign_worker_ranks` in `api.py`): `WORLD_SIZE=2`, `LOCAL_WORLD_SIZE=1`, `LOCAL_RANK=0`, and `RANK` 0 on node 0, 1 on node 1. The pinned `initialize_distributed` then calls `torch.cuda.set_device(0)` in both ranks, and device 0 is a different physical GPU in each: the GPU that rank has under the launcher `triton-dist`. The programs derive `nnodes = WORLD_SIZE // LOCAL_WORLD_SIZE = 2`. A rank whose `LOCAL_WORLD_SIZE` is not `ranks / logical_nodes` is stopped by `gpurun` before the harness is called.

Design choice. The alternative was a launcher of our own that starts every rank itself and sets `RANK`, `LOCAL_RANK`, `WORLD_SIZE`, `LOCAL_WORLD_SIZE`, the torch rendezvous variables and the NVSHMEM settings. Starting the pinned script once per logical node was chosen because it keeps the pinned NVSHMEM settings and torchrun, and is about twenty lines of new code. It relies on:

1. the script's multi-node variables keeping the meaning read at the pin;
2. torchrun's static rendezvous accepting two agents on one host, where the agent with node rank 0 hosts the store at the endpoint and the other connects to it (read in `torch/distributed/elastic/rendezvous/static_tcp_rendezvous.py`; not run);
3. torchrun handing its own environment, `CUDA_VISIBLE_DEVICES` included, to each rank (read in `torch/distributed/elastic/multiprocessing/subprocess_handler/subprocess_handler.py`);
4. NCCL and NVSHMEM reaching a GPU that the process cannot see (next subsection).

Each logical node sees only its own GPUs, as a node of a real cluster does. If a GPU run shows that item 4 fails, the fallback is to leave every GPU visible to every logical node and list the node's own GPUs first: NVSHMEM and NCCL then see the peer as they do under `triton-dist`, but a program that counts visible devices sees more than a real node has. The fallback is not implemented.

### Transport expected between the two GPUs

This subsection is an expectation from source, not an observation. Library source is used only to predict whether a run starts; it defines no semantics.

Sources, all read on github.com on 2026-11-12:

- NVSHMEM: [`NVIDIA/nvshmem` at tag `v3.6.5-0`](https://github.com/NVIDIA/nvshmem/tree/6e53a40d9db16df170b3b0057e94c340d72f77eb), commit `6e53a40d9db16df170b3b0057e94c340d72f77eb`. The pinned `python/setup.py` of Triton-distributed requires `nvidia-nvshmem-cu12==3.6.5`.
- NCCL: [`NVIDIA/nccl` at tag `v2.27.3-1`](https://github.com/NVIDIA/nccl/tree/72d2432094d6ae36abd6e511c3a16a2d052dbf94), commit `72d2432094d6ae36abd6e511c3a16a2d052dbf94`. PyTorch 2.8.0 requires `nvidia-nccl-cu12==2.27.3` for CUDA 12.6 (`.github/scripts/generate_binary_build_matrix.py`).
- PyTorch: [`pytorch/pytorch` at tag `v2.8.0`](https://github.com/pytorch/pytorch/tree/ba56102387ef21a3b04b357e5b183d48f0afefc7), commit `ba56102387ef21a3b04b357e5b183d48f0afefc7`.

Installed on the GPU side, by the `env.json` of `internode-logical-env-002`: PyTorch `2.8.0+cu126`, the NVSHMEM library `3.6.5`, the NVSHMEM bindings `0.3.0`, Triton `3.7.1`. Not confirmed: the NCCL version, which `env.json` does not report.

Read in source:

- NVSHMEM identifies a host by a hash of `gethostname()` (`src/host/util/util.cpp`, `nvshmemu_getHostHash`). Nothing the launcher sets enters it.
- Its P2P transport (`src/host/transport/p2p/p2p.cpp`, `nvshmemt_p2p_can_reach_peer`) does not reach a peer with another host hash. For a peer with the same hash it looks for the peer's GPU among the devices the process sees. When it finds it, it asks `cudaDeviceCanAccessPeer`. When it does not, which the source attributes to `CUDA_VISIBLE_DEVICES`, and the CUDA driver is version 12 or later or the heap is not the VMM heap, it asks NVML for the P2P status of the two devices and grants the mapping when read and write are allowed. Otherwise it warns that it uses a network transport.
- A peer that no transport reaches ends initialization with the message `Peer GPU … is not accessible` (`src/host/topo/topo.cpp`, `nvshmemi_build_transport_map`).
- NCCL, which `initialize_distributed` uses for its process group, treats two ranks as local when their host hashes agree; where a peer's device is not visible to the process, its P2P check carries the comment `CUDA 10.1 and later can use P2P with invisible devices` (`src/transport/p2p.cc`).

Inferred: both logical nodes have the same host hash, so NVSHMEM is expected to use its P2P transport between the two GPUs, that is, the mapping of the peer's symmetric heap that an ordinary one-node run uses, over the NVLink of the pair. It is reached through the NVML branch, because each logical node hides the other's GPU. No NIC and no remote transport (IBRC, UCX, IBGDA, libfabric) is expected to carry data.

### What a logical-node run exercises

Source reading at the pin for two logical nodes of one local rank each (`WORLD_SIZE=2`, `LOCAL_WORLD_SIZE=1`, `nnodes=2`):

| Program | Reached with two logical nodes of one rank | Still not reached |
| --- | --- | --- |
| Tutorial 03 | `NNODES=2`. In `all_gather_push_2d_kernel` every program has `peer_local_rank == local_rank`: the program of the other rank does the cross-node `putmem_signal_nbi_block`, the program of the own rank waits for the peer's signal. | The intra-node branch, with its wait for a segment from another node before forwarding it. It needs a peer with another local rank: two local ranks on each of two nodes, four GPUs. |
| Tutorial 06 | `nnodes=2`. `kernel_inter_node_p2p_for_same_local_rank` is launched (for `n = 0`), the result is taken from the P2P buffer, and `ring_reduce` runs over two nodes. This needs a context that the tutorial's own constructor does not deliver outside node 0 (subsection "The tutorial requests"). | `intra_node_scatter` to another local rank: with one local rank it copies into the rank's own buffer. |
| All-to-all inter-node kernel | With `local_world_size=1` passed explicitly, `nnodes=2`, so the pull loop meets `src_node != node_id` and waits for the other node's signal. Read at these lines only; the kernel was not traced further. | Transfer between different local ranks of the receiving node. |
| Sequence-parallel all-gather attention inter-node kernel | Its push kernel has the structure of tutorial 03's 2D kernel: the cross-node put to the same local rank. Read at these lines only. | The intra-node forwarding branch, as for tutorial 03. |

The launcher also starts four ranks as two logical nodes of two (`ranks` 4, `logical_nodes` 2; tested with the stand-in), which reaches the forwarding branches. That takes four GPUs in one request; the rule for this host is two, and the user has permitted the exception for one request per tutorial. The subsection "The tutorial requests" has the branches of tutorials 03 and 06 by line, and what the reading found on the way; the subsection after it has the two requests with four ranks.

### What it does not exercise

- A NIC, or an RDMA or IBGDA transport: data is expected to move by GPU peer-to-peer mapping inside one host.
- NVSHMEM bootstrap, NCCL and the torchrun rendezvous across hosts: all three connect within one host.
- Isolation between hosts: the logical nodes share the operating system, the host name, the file system (the Triton cache directory included) and the CPU memory.
- A node boundary as NVSHMEM sees it. NVSHMEM puts the ranks whose host-name hashes agree into one node team (`init_team_node`, `src/host/team/team_internal.cpp:1106-1130` at tag `v3.6.5-0`; read on 2026-11-12, not run), so both logical nodes are one NVSHMEM node. Code that asks NVSHMEM which ranks share its node, instead of reading `LOCAL_WORLD_SIZE`, sees one node of all ranks. The intra-node barrier of tutorial 06 is such code (subsection "The tutorial requests").
- Latency, bandwidth and timing of a network between nodes.
- Failures: a lost node, a lost link, a partition.

A logical-node result therefore shows the control flow and the rank arithmetic of the `nnodes > 1` branches, and that data addressed to a rank of another node arrives, with the transport of a one-node run. It is evidence about the program text, not about communication between hosts. `gpurun` labels it: `meta.json` says `"topology": "logical-nodes"` with `logical_nodes` and `local_ranks`; `requires.nodes` and `GPURUN_NODES` stay 1; and a logical-node test in a batch that requires more than one physical node returns `skipped_env`.

### What only a run on the GPU side can settle

Each of the first seven points is followed by its state after `internode-logical-env-002` (next subsection), and points 7 to 10 by their state after the two tutorial requests with one rank per logical node. "Settled" means observed in the batch named: two repeats, on one pair of GPUs.

1. Whether two torchrun agents on one host meet at the loopback endpoint, and whether the fixed port `23456` is free: another job on the shared host, or the store of the previous repeat, may hold it. **Settled for that run:** in both repeats the two agents met at port `23456` of the loopback address and every rank started. Whether the port is free stays a question of each run.
2. Whether each rank gets the expected `RANK`, `LOCAL_RANK`, `WORLD_SIZE` and `LOCAL_WORLD_SIZE`. **Settled:** the ranks reported the expected values (table in the next subsection).
3. Whether NCCL forms the process group between two ranks that each see one GPU. **Settled:** `initialize_distributed` returned in both ranks; it creates the NCCL group over all ranks and runs a barrier on it (`python/triton_dist/utils.py:355-356` at the pin).
4. Whether the NVSHMEM UID bootstrap completes across the two launcher groups. By the source it sees only the unique identifier, the rank and the rank count that `initialize_distributed` passes, not the groups. **Settled:** NVSHMEM initialized in both ranks, and the barriers and the put after it completed.
5. Whether NVSHMEM reaches the hidden peer GPU through NVML and maps its heap, or stops with `Peer GPU … is not accessible`; and which NVSHMEM library version is installed. **Settled in its outcome:** initialization did not stop, the put landed, and the logs hold neither that message nor a warning about a network transport. Which branch of the source granted the mapping is not in the logs. The installed library is `3.6.5` (`env.json`).
6. Whether a put to the rank of the other logical node arrives, and whether `nvshmem.core.put` of the installed bindings accepts the call of the harness. **Settled:** every rank received the four values of the other rank. Not settled, and not touched by that batch: the one host-side put at the pin, which goes through the low-level binding, `pynvshmem.putmem_on_stream` in `python/triton_dist/kernels/nvidia/reduce_scatter.py` (`reduce_scatter_for_each_node_ring`, under `nnodes > 1`), called with four arguments where the binding at NVSHMEM tag `v3.6.5-0` declares five, the stream last (`nvshmem4py/nvshmem/bindings/nvshmem.pyx:1615`). Tutorial 06 does not reach that call (subsection "The tutorial requests"), so its request will not settle it either.
7. Whether two logical nodes that compile at the same time into the one Triton cache directory disturb each other. **Settled for those runs:** the environment batch compiled no kernel; in the first repeat of each `logical_nodes` test of the two tutorial requests both logical nodes compiled the same kernels at once, and every such test ended `ok` with the expected tensors. Two processes; four are not observed.

Added with the tutorial requests:

8. Whether any kernel of tutorials 03 and 06 compiles and runs in the installed environment. The `one_node` control tests answer this apart from the logical nodes. **Settled:** both kernels of tutorial 03 and the kernels that tutorial 06 launches ran under both launchers.
9. Whether Triton's JIT compiles a kernel of tutorial 03 from a module that holds only the definitions of the file, which is how the harness avoids running the tutorial's program. On the development host this is tested only as far as `inspect.getsourcelines`, which the JIT reads the kernel with, returning the text of the file. **Settled:** all four tests of `internode-logical-ag03-001` compiled their kernel that way.
10. What NVSHMEM's node team reports under logical nodes (expected from source: all ranks of the host), and whether the intra-node barrier of tutorial 06, which uses it, completes across the two logical nodes. **Settled:** under both launchers rank r reported local rank r of a node team of 2 and native atomics 1, and the barrier completed.

Added with the requests with four ranks (subsection "The requests with two logical nodes of two ranks"):

11. Whether NVSHMEM reaches a GPU of the other NVLink pair and maps its memory: through `cudaDeviceCanAccessPeer` where the GPU is visible (`one_node`), through the NVML status of the two devices where it is hidden (`logical_nodes`). If it does not, initialization stops with `Peer GPU … is not accessible` in every test of both requests.
12. Whether NCCL forms the process group over four ranks, under one launcher group of four and under two groups of two.
13. **Observed in #511.** Under `one_node`, every rank reported native atomics as `0-1:1 0-2:0 0-3:0 1-2:0 1-3:0 2-3:1`. Every pair spanning the two NVLink pairs reported 0. Under `logical_nodes`, each rank saw its own pair and reported `0-1:1`.
14. What the compare-and-swap kernel of tutorial 06's barrier does on memory reached over a link that reports no native atomic operations: it completes, it hangs, or the GPU reports an error. No document read here says which.
15. Whether a host-side copy into the tensor of a rank on the other pair arrives (`one_node/harness_context` of the tutorial 06 request: every rank scatters to three ranks, two of them on the other pair).
16. Whether the receive-then-forward branch of tutorial 03 and the scatter followed by the inter-node put of tutorial 06 return the expected tensors.

### First request and its result

`internode-logical-env-001` (`experiments/interp_gpu/batches/internode-logical-env-001/`, harness `experiments/interp_gpu/smoke/dist_logical_nodes.py`) addresses items 1 to 6 without a tutorial kernel. Each rank initializes through the pinned `initialize_distributed`; reports its rank, the world size, `LOCAL_WORLD_SIZE`, the derived node count, `LOCAL_RANK` and its CUDA device index as a tensor; prints its device name; puts four values into the other rank's symmetric memory between two barriers; and stops. The first barrier is there so that no put lands before the receiver has initialized its buffer.

The batch has two tests with the same harness: `one_node/put_barrier` under `triton-dist` as the control, and `logical_nodes/put_barrier` under the new launcher, so that a failure of the harness itself is told apart from a failure of the logical nodes. The development side expects: under the control, `LOCAL_WORLD_SIZE` 2, one node, device index equal to the rank; under the logical nodes, `LOCAL_WORLD_SIZE` 1, two nodes, device index 0 in both ranks; in both, every rank receives 100 plus the number of the other rank.

Result. `internode-logical-env-001` ran on the GPU side with every test `ok`, and its bundle was not published: the launcher's log holds the loopback address, and the rule for public results did not yet allow an address in a log. `gpurun` now writes that address as `<loopback>`, and the same request ran again as `internode-logical-env-002` on 2026-11-12 ([issue #430](https://github.com/VeriInfra-Lab/VeriTile-2/issues/430); request commit `ad26d295f4f8737ab82df8312a7eed21bbc4366c`; bundle `results/internode-logical-env-002/` at commit `3ff8914868fa562c7dff6caac9344627732c4ce4` of the branch `gpu-results`). Both tests ended `ok` with both ranks `ok` in both repeats, on the NVLink pair 4–5. Decoded on the development side, equal in both repeats:

| Test | Rank | `topology` (rank, world size, `LOCAL_WORLD_SIZE`, nodes, `LOCAL_RANK`, device index) | `received` |
| --- | --- | --- | --- |
| `one_node/put_barrier` | 0 | 0, 2, 2, 1, 0, 0 | 101 four times |
| `one_node/put_barrier` | 1 | 1, 2, 2, 1, 1, 1 | 100 four times |
| `logical_nodes/put_barrier` | 0 | 0, 2, 1, 2, 0, 0 | 101 four times |
| `logical_nodes/put_barrier` | 1 | 1, 2, 1, 2, 0, 0 | 100 four times |

Every value is the expected one, so the batch was judged pass: two logical nodes of one rank each come up on the one host through the pinned launcher, each rank sees only its own GPU, the runtime derives two nodes, and a put to the rank on the other logical node lands. The previous subsection says what this settles.

### The tutorial requests

Written on 2026-11-12; both ran on the GPU side the same day and were judged on 2026-11-13 ("Results" at the end of this subsection). `internode-logical-ag03-001` and `internode-logical-rs06-001` (under `experiments/interp_gpu/batches/`) call the functions of tutorials 03 and 06 on small fixed inputs with 2 ranks. Every test under `logical_nodes/` (launcher `triton-dist-logical-nodes`, two logical nodes of one rank) has a twin under `one_node/` (launcher `triton-dist`) with the same harness, inputs and outputs, so that a failure of the tutorial is told apart from a failure of the logical nodes. Every rank returns its result tensors and the `topology` values of the environment batch. The harness is `experiments/interp_gpu/internode_logical/harness.py`. Beside it, `judge.py` computes the expected tensors from the regenerated inputs with the Python standard library and prints `equal` or `different` per test, rank and output, and `test_internode_logical.py` tests both without a GPU. No tutorial file is edited or copied: the harness reads it from the checkout that the environment was built from. The batches were committed without an issue or a label and announced by the coordinator afterwards.

`T03:n`, `T06:n`, `RS:n`, `CO:n` and `UT:n` are lines of `tutorials/03-inter-node-allgather.py`, `tutorials/06-inter-node-reduce-scatter.py`, `python/triton_dist/kernels/nvidia/reduce_scatter.py`, `python/triton_dist/kernels/nvidia/common_ops.py` and `python/triton_dist/utils.py` at the pin, as in [dist/EventControlFlow.md](dist/EventControlFlow.md). Everything in this subsection before "Results" is read from source on 2026-11-12 or inferred from it, and was written before the run.

**Tutorial 03, `internode-logical-ag03-001`.** Four tests: the kernels `push_1d` and `push_2d` under each launcher. Input: 64 bytes, the same in every rank; rank r owns bytes 32r to 32r + 31. The buffer of a rank starts with its own segment and the sentinel elsewhere, and comes back after one kernel call as `gathered`. Expected: every test `ok`, and `gathered` equal to the 64 input bytes in every rank.

| Kernel text | `one_node` (one node of two ranks) | `logical_nodes` (two nodes of one rank) | Left for two nodes of two ranks |
| --- | --- | --- | --- |
| `all_gather_push_1d_kernel` (`T03:62-95`); it has no branch on the node count | A put with signal to the other rank (`T03:85-95`) and a wait for its signal (`T03:72-76`). | The same. | Nothing. |
| `all_gather_push_2d_kernel`, a program of the same local rank and another rank (`T03:135-147`): the cross-node `putmem_signal_nbi_block` | Not reached. | Reached: every program has `peer_local_rank == local_rank`, and the program of the other rank puts the rank's segment to the other node. | Nothing. |
| The same kernel, the program of the rank itself (`T03:148-155`): the wait for every peer's signal | Reached. | Reached. | Nothing. |
| The same kernel, a program of another local rank (`T03:156-177`): the intra-node `putmem_signal_block` | Reached, without the wait of `T03:160-167`, because `peer_node_id == node_id`. | Not reached. | The wait for a segment from the other node before it is forwarded inside the node (`T03:160-167`). |

Read on the way:

- **The tutorial runs its whole program at import.** The file has no `__main__` guard: `T03:256-299` start the runtime, draw random data, time both kernels and stop the runtime. The harness therefore executes only the top-level imports, classes and functions of the file. It filters the syntax tree and compiles it under the name of the file, so that Triton's JIT still reads the unchanged kernel text at its lines. The harness is itself the program around these definitions: one buffer of 64 bytes and one kernel call per test, where the tutorial has a double buffer and a timing loop.
- **Signal tensors: the reading of observation 5 in section 8 of `dist/EventControlFlow.md` is confirmed from source.** `T03:276-278` create each signal tensor with shape `(1, )`, one 8-byte word (`UT:572`); `T03:103` and `T03:185` pass one of them as `symm_flag`. The 1D kernel waits on `symm_flag + peer` for every `peer` below `WORLD_SIZE` other than the rank (`T03:68-76`) and signals `symm_flag + segment` with `segment = rank` (`T03:81`, `T03:91`). The 2D kernel does the same at `T03:138-143`, `T03:149-154`, `T03:158-163` and `T03:173`. With two ranks, rank 1 sets word 1 of the tensor on rank 0 and rank 0 waits on that word: one word past what the tutorial allocated. So the tutorial's program accesses memory outside the tensor whenever `WORLD_SIZE > 1`, under one node as under two; whether the allocator leaves that word unused is not known. The batch does not run that program. The harness allocates `ranks` words per signal tensor and states it. Running the tutorial as written was not chosen because no outcome would show the defect: a pass does not refute it, and a hang, a wrong byte or an allocator error could each have another cause.

**Tutorial 06, `internode-logical-rs06-001`.** The file has a `__main__` guard (`T06:448`) and is imported whole. Input: per rank a 512 by 128 matrix of integers between -100 and 100, converted to bfloat16, the dtype of the tutorial (`T06:458`). `reduce_scatter_2d_op` (`T06:410-433`) is called as the tutorial's `__main__` calls it, between the same two barriers (`T06:474-479`), and what it returns comes back as `reduced`. Expected in rank r: rows 256r to 256r + 255 of the sum of the two matrices. Every sum is an integer of magnitude at most 200, which bfloat16 holds exactly, so the comparison has no tolerance. The shape is the smallest for which every tile of `kernel_ring_reduce_tma` (256 rows by 64 or 128 columns, `RS:749-775`) lies inside its tensors, as with the tutorial's own 8192 by 16384; a smaller matrix would also test how a tile behaves across the border of a tensor, which is not the subject.

| Text | `one_node` (one node of two ranks) | `logical_nodes` (two nodes of one rank) | Left for two nodes of two ranks |
| --- | --- | --- | --- |
| The loop over nodes (`T06:314`) | One pass: the own node. | Two passes: the other node, then the own. | Nothing. |
| `intra_node_scatter` (`T06:264-294`), host copies | Into the buffer of the other rank. | Into the rank's own buffer (`remote_local_rank == local_rank`). | A copy to another local rank in each of two passes. |
| `barrier_all_on_stream` (`T06:344`) | The intra-node barrier kernel over two ranks. | The same kernel, expected over two ranks, where a real node of one rank would run it over one (below). | Nothing. |
| `ring_reduce` per node (`T06:349-354`) | A sum of two blocks. | A copy of one block (`num_splits` is 1). | A sum of two blocks per pass. |
| Under `nnodes > 1` (`T06:357`), last pass (`T06:358-363`): the rank's own result is copied to the P2P buffer | Not reached. | Reached, second pass. | Nothing. |
| Under `nnodes > 1`, other passes (`T06:364-374`): `kernel_inter_node_p2p_for_same_local_rank`, one `putmem_block` to the same local rank of the other node (`T06:256-261`) | Not reached. | Reached, first pass. | Nothing. |
| The value returned (`T06:377-379`) | The per-node buffer. | The P2P buffer. | Nothing. |
| `ring_reduce` over nodes (`T06:406`) | A copy of one block (`num_splits = nnodes = 1`). | A sum of two blocks, one of them received from the other node. | Nothing. |

Four tests: `tutorial_context` and `harness_context` under each launcher. Read on the way:

- **The context constructor of the tutorial fails outside node 0: a predicted failure.** `create_reduce_scater_2d_ctx` gets its signal tensors from `nvshmem_create_tensors(..., rank, local_world_size)`, a list with one entry per rank of the caller's node (`UT:257-272`), and then takes `signal_bufs[rank]` with the global rank (`T06:199-202`). In a rank of node 0 that is the rank's own tensor. In any other rank the index is past the end of the list: `IndexError: list index out of range`, before any kernel is launched. So tutorial 06 as written cannot run with more than one node, logical or physical. The request exposes this and also goes around it, in separate tests:
  - `*/tutorial_context` calls the tutorial's constructor as its `__main__` does (`T06:460-466`). Under `one_node` it is expected to work. Under `logical_nodes` rank 1 is expected to raise the `IndexError`, and rank 0 is then expected to wait for it in the barrier of `T06:205` until the timeout of that test, 240 s. The expected status of `logical_nodes/tutorial_context` is `timeout` or `runtime_error`, with `runtime_error` for rank 1 and the `IndexError` in `stderr.log`. The judge calls that `failed as predicted`, and anything else `prediction not met`. This failure is the wanted result of the test; the notes of the batch say so to the GPU side.
  - `*/harness_context` builds the same `ReduceScatter2DContext` in the harness, with the allocations and values of `T06:188-229` and that one index taken within the node (`rank % local_world_size`). Everything after it is the tutorial's. `logical_nodes/harness_context` is the test that reaches the `nnodes > 1` branches of the table.
- **`putmem_on_stream` is not reached.** Tutorial 06 defines its own `reduce_scatter_for_each_node` and `reduce_scatter_multi_node` (`T06:297`, `T06:382`) and imports only `ring_reduce` from the library file (`T06:49`). The four-argument call of `pynvshmem.putmem_on_stream` is in `reduce_scatter_for_each_node_ring` (`RS:538-543`). Its one caller is the library's `reduce_scatter_multi_node`, when `has_fullmesh_nvlink()` is false (`RS:807-808`); tutorial 08 reaches that function, tutorial 06 does not. So this batch is not expected to show a `runtime_error` from that call, and the call stays unexercised by every batch of this document.
- **The intra-node barrier does not see the logical nodes.** The context holds `BarrierAllContext(True)` (`T06:223`), which takes its local rank and its node size from NVSHMEM's node team (`CO:238-240`), not from `LOCAL_WORLD_SIZE`. Both logical nodes are one NVSHMEM node (subsection "What it does not exercise"). Under `logical_nodes` the barrier of `T06:344` is therefore expected to run over both ranks. Both ranks call it equally often, once per pass, so it is expected to complete: it synchronizes more than the text intends for a node of one rank, not less. Every rank returns the local rank and the node size of the barrier in `barrier`; expected r and 2 under both launchers.
- **Native atomics are assumed under logical nodes.** `barrier_all_on_stream` launches the compare-and-swap kernel when `supports_p2p_native_atomic()` holds (`CO:257-258`). That function returns true without asking the driver when the process sees one GPU (`UT:536-538`), as every rank of a logical node of one does; under `one_node` it asks the driver about the pair (`UT:544-547`). The docstring of the kernel forbids it where the link between the GPUs has no atomics (`CO:155-157`). The third value of `barrier` is the answer of that function: expected 1 under both launchers on an NVLink pair (inferred from that docstring, which names PCIe as the case without atomics). A 0 under `one_node` would mean that the `logical_nodes` test used atomic operations on a pair that reports none. The request belongs on an NVLink pair, as the environment batch ran.

**Results.** Both requests ran once on the GPU side on 2026-11-12, at request commit `4e9a91a52577f00649442e2454b8bb51cbab42a7`, on the NVLink pair 4–5, and were judged on the development side on 2026-11-13 with `judge.py`, which exits 0 for both bundles (repeated for this document on 2026-11-13).

| Request | Issue | Bundle on `gpu-results` | Status per test | Judged |
| --- | --- | --- | --- | --- |
| `internode-logical-ag03-001` | [#434](https://github.com/VeriInfra-Lab/VeriTile-2/issues/434) | `results/internode-logical-ag03-001/` at `c8bc3631b45c9b2071ddf52e0b9de0394d4c6425` | Four tests `ok`, two repeats each, both ranks `ok` | Pass: in every test both ranks return the expected `topology` and the 64 input bytes, in both repeats. |
| `internode-logical-rs06-001` | [#435](https://github.com/VeriInfra-Lab/VeriTile-2/issues/435) | `results/internode-logical-rs06-001/` at `326fa57e4a063af67062a4b3cf48865824b3609c` | Three tests `ok`, two repeats each; `logical_nodes/tutorial_context` `timeout` after 239.9 s with rank status none for rank 0 and `runtime_error` for rank 1 | Pass, with the predicted failure observed: the three tests return the expected `topology`, `barrier` and `reduced` in both ranks and repeats (exact, no tolerance); the fourth is `failed as predicted`. |

What the results establish, each for one run of two repeats on one pair:

- Tutorial 03: with one rank per logical node the 2D kernel runs its cross-node put and its wait (`T03:135-155`) and every rank holds the whole input afterwards. The kernels are unchanged; the signal tensors are the harness's, of one word per rank. The receive-then-forward branch (`T03:156-177` with the wait of `T03:160-167`) did not run.
- Tutorial 06 as written cannot start on more than one node: rank 1 raised `IndexError: list index out of range` at `T06:202`, before any kernel, and rank 0 waited until the timeout. This is observed, not only read.
- Tutorial 06 with the context built by the harness: the inter-node P2P kernel (`T06:364-374`) and the reduction over two nodes (`T06:406`) run on two logical nodes and every rank returns its rows of the exact sum. **Decision (user, 2026-11-13):** this run counts as the run of tutorial 06 on logical nodes; the deviation, one host-side index with the kernels unchanged, stays recorded.
- Under both launchers every rank reported local rank r of a node team of 2: NVSHMEM's node team spans both logical nodes, as read. Both launchers reported native atomics 1; under `one_node` that is the driver's answer for the pair 4–5.
- A scatter to another local rank under `nnodes > 1` did not run: with one rank per node `intra_node_scatter` copies into the rank's own buffer.

**Decision (user, 2026-11-13).** The defects found in the pinned tutorials are not reported upstream now. They are collected and, where confirmed, reported near the end of the project.

### The requests with two logical nodes of two ranks

The following analysis records the original requests of 2026-11-13. Tutorial 03 has since passed (#466). The user withdrew the original tutorial 06 request before announcement on 2026-11-21. The replacement below retains the four-GPU exception in section 9 of [GpuExchangeProtocol.md](GpuExchangeProtocol.md).

Each has 4 ranks. A test under `logical_nodes/` runs under `triton-dist-logical-nodes` with `logical_nodes` 2: `WORLD_SIZE=4`, `LOCAL_WORLD_SIZE=2`, two nodes of two ranks, rank = 2 × node + local rank. Its twin under `one_node/` runs the same harness, inputs and outputs under `triton-dist`: one node of four ranks. Harness and judge are those of the requests with 2 ranks. The judge computes its references for any number of ranks; `test_internode_logical.py` plants wrong results for four ranks and checks that each is flagged.

**Visible order.** The launcher gives logical node n entries 2n and 2n + 1 of the operator's `CUDA_VISIBLE_DEVICES` (`logical_nodes` in `scripts/gpurun/dist.py`), and rank r runs on entry r under both launchers. The operator therefore lists the two GPUs of one pair, then the two of another: `0,1,2,3`, `2,3,4,5` or `0,1,4,5`. Each logical node then holds one NVLink pair: traffic inside a logical node has NVLink, and traffic between the logical nodes crosses from one pair to the other, as inside and between the nodes of a cluster. An order such as `0,2,1,3` would put the NVLink between the logical nodes instead. `gpurun` does not know which GPUs form a pair, so the order is the operator's; it refuses nothing that four GPUs need, and with fewer than four visible GPUs the batch and each of its tests return `skipped_env` (`scripts/gpurun/test_dist.py`, and for these two batches `test_internode_logical.py`).

**Tutorial 03, `internode-logical-ag03-2x2-001`.** The four tests of the request with 2 ranks, on the same 64 bytes; rank r owns bytes 16r to 16r + 15. Read at the pin: the 2D kernel is launched with one program per rank (`T03:182`) and splits a rank into node and local rank (`T03:125-131`). With two nodes of two, the four programs of rank r are:

| Program of rank r | Lines | What it does |
| --- | --- | --- |
| r | `T03:148-155` | Waits, one thread per other rank, for the signal words of the three other segments. |
| r xor 2: same local rank, other node | `T03:135-147` | Cross-node put with signal, not blocking, of segment r to rank r xor 2. |
| r xor 1: other local rank, same node | `T03:156-159`, `T03:169-177` | Put with signal of segment r to rank r xor 1. No wait before it, because `peer_node_id == node_id`. |
| 3 − r: other local rank, other node | `T03:156-177` | **Receive, then forward.** Thread 0 waits for signal word r xor 2, which rank r xor 2 sets when its segment has arrived in rank r (`T03:160-166`); all threads join (`T03:167`); the program then puts segment r xor 2 with signal to rank r xor 1 (`T03:169-177`). |

So the receive-then-forward lines run in all four ranks, in one program each. Rank r gets segment r xor 1 directly from the other rank of its node, segment r xor 2 from the other node, and segment 3 − r forwarded by rank r xor 1, which received it from rank 3 − r. Under `one_node` (`NNODES=1`) every program other than r takes `T03:156-159` and `T03:169-177` with `peer_node_id == node_id`: three direct puts, no cross-node put and no wait before a put. A segment that was forwarded before it arrived holds the sentinel in the receiving rank, although its signal is set; the judge names the segments that differ.

What changes against the run with one rank per logical node, besides the branch:

- Signal words. The kernels address words 0 to 3 (`T03:143`, `T03:151`, `T03:163`, `T03:173`). The harness allocates four words per signal tensor; the tutorial's program allocates one (`T03:276-278`), so with four ranks it would use three words past its tensor.
- Sizes. Four programs per launch; 16 bytes per put.
- Barriers. The harness's two barriers are NVSHMEM's own over all four ranks (`UT:304-306`).
- Links. Under `logical_nodes` the puts inside a node stay on one NVLink pair and the cross-node put of every rank goes to the other pair. Under `one_node` every rank puts directly to three ranks, two of them on the other pair.

Not reached by this request and not needed by it: `supports_p2p_native_atomic()` and `has_fullmesh_nvlink()`. Tutorial 03 imports neither (`T03:44-47`).

**Tutorial 06, `internode-logical-rs06-2x2-001`.** Two tests, `one_node/harness_context` and `logical_nodes/harness_context`: only the context built by the harness, because the tutorial's own constructor fails outside node 0 (observed above; the test of that failure is not repeated). Input: per rank a 1024 by 128 matrix of integers between −64 and 64, converted to bfloat16. Expected in rank r: rows 256r to 256r + 255 of the sum of the four matrices. The sum of any of the four inputs has magnitude at most 256, which bfloat16 holds exactly, so the comparison has no tolerance whatever the order of the additions. With 1024 rows every reduction tile again lies inside its tensors (256 rows per rank).

Read at the pin for `world_size` 4 and `local_world_size` 2 (`nnodes` 2, `M_per_rank` 256, `M_per_node` 512):

| Text | `one_node` (one node of four ranks) | `logical_nodes` (two nodes of two ranks) |
| --- | --- | --- |
| Buffers (`T06:188-201`, built in the harness) | Scatter 1024 rows; per-node and P2P 256 rows; 8 signal words; every list has four tensors, three of them the tensors of peers. | Scatter 1024 rows; per-node and P2P 512 rows; 8 signal words; every list has two tensors, the rank's own and that of the other rank of its node. |
| The loop over nodes (`T06:314`, `T06:326`) | One pass. | Two passes: the rows for the other node, then those for the own node. |
| `intra_node_scatter` (`T06:276-294`) | Host copies of 256 rows into the scatter buffers of the three other ranks and into the rank's own. | In each pass a host copy of 256 rows **into the scatter buffer of the other rank of the node** (`T06:279`, `T06:288-294`, first iteration) and one into the rank's own: the branch this request is for. All four ranks take it, twice. |
| `barrier_all_on_stream` (`T06:344`) | Once, over the node team of four ranks. | Twice, over the same node team of four ranks, not over the node of two (below). |
| `ring_reduce` per node (`T06:349-354`) | A sum of four blocks of 256 rows. | Per pass a sum of two blocks of 256 rows: the rank's rows of that pass as its own node holds them. |
| Under `nnodes > 1` (`T06:357-374`) | Not reached. | First pass: `kernel_inter_node_p2p_for_same_local_rank` puts the 256 rows of the node's partial sum to rank r xor 2 (`T06:253-261`). Second pass: the node's partial sum for the rank itself is copied to its P2P buffer (`T06:358-363`). |
| `ring_reduce` over nodes (`T06:406`) | A copy of one block. | A sum of two blocks: the partial sum of the own node and the one received from the other node. |

So a result of `logical_nodes/harness_context` depends on the scatter to the other local rank (each partial sum has the rows the other rank scattered), on the inter-node put, and on both reductions.

**The barrier of tutorial 06 is outside what its text allows on four GPUs of this host.** This holds under both launchers, and no visible order avoids it:

- The context holds `BarrierAllContext(True)` (`T06:223`), whose rank count is the size of NVSHMEM's node team (`CO:238-241`). All four ranks have the same host-name hash, so the team has four ranks under one node and under two logical nodes (`init_team_node`, `src/host/team/team_internal.cpp:1106-1130` at `v3.6.5-0`; with two ranks observed in #435).
- `barrier_all_on_stream` launches the compare-and-swap kernel when `supports_p2p_native_atomic()` holds (`CO:257-258`). That function asks the driver about visible devices 0 and 1 only (`UT:544-547`). Under `one_node` devices 0 and 1 are the first pair. Under `logical_nodes` a rank sees the two GPUs of its own pair. With the visible order pair, pair the answer is therefore expected to be 1 in every rank (the pair 4–5 answered 1 in #435), and every rank launches the compare-and-swap kernel.
- In that kernel each rank does `atomic_cas` on a word in the memory of every rank of the team (`CO:158-163`): one rank on its own NVLink pair and two on the other pair, reached over PCIe. The docstring of the kernel says that memory over PCIe does not support atomic operations and that the kernel must not be used there (`CO:155-157`).
- With another order, in which visible devices 0 and 1 are not a pair, the answer is expected to be 0 and `barrier_all_on_stream` launches `barrier_all_intra_node_non_atomic_block` instead (`CO:259-262`). That kernel needs twice as many flag words as ranks (`CO:185-196`: its second round uses `symm_flags + num_ranks`), and the context allocates one word per rank (`CO:241`). So that path uses words past its tensor, with any number of ranks. It is a second defect read on the way, not run.

Predicted outcome of both tests: not determined by anything read. The request is delivered because each outcome is informative and the cost is bounded (300 s per test):

- `ok` and `equal`: the scatter, the inter-node put and the reductions computed the expected rows on this host while the barrier ran outside its stated condition. That is evidence for those lines. It is not evidence that the barrier is correct over such a link.
- `timeout`: the barrier, or something before it, did not complete; the log shows the last line each rank printed.
- `runtime_error`: the log has the error.

Inferred, not a guarantee: if the GPU carries out the compare-and-swap over PCIe as a read followed by a write, the barrier still completes, because each flag word is changed by one rank while it is 0 and by one other rank while it is 1 (`CO:161-167`). Whether the GPU does that, refuses the operation or reports an error is not documented in anything read here.

To make the result readable, every rank prints, besides the barrier's team and the answer of `supports_p2p_native_atomic()` (returned as `barrier`), what the driver reports for native atomic operations between each pair of its visible devices. Under `one_node` that is all six pairs of the four GPUs. The judge expects `barrier` to be r, 4, 1 under both launchers; a 0 in the third place means the first two visible devices were not an NVLink pair.

Not reached by this request: `has_fullmesh_nvlink()`. Tutorial 06 imports only `ring_reduce` from the library file (`T06:49`), and `ring_reduce` asks `has_tma()` (`RS:787-790`). From its text (`python/triton_dist/nv_utils.py:199-216`, `298-309`) it would answer false in a process that sees both pairs and true in a process that sees one pair, so the library's `reduce_scatter_multi_node` (`RS:807-810`), which tutorial 08 calls, would take different host paths under the two launchers.

**Transport expected between GPUs of different pairs.** An expectation from the NVSHMEM source at `v3.6.5-0` (read on 2026-11-13; the sources and their use are those of the subsection "Transport expected between the two GPUs"), not an observation:

- The P2P transport grants load and store on a peer's memory when the peer is on the same host and either `cudaDeviceCanAccessPeer` holds (peer visible) or NVML reports read and write as allowed between the two devices (peer hidden). It adds the capability for atomic operations only when `cudaDeviceGetP2PAttribute` reports native atomics, or NVML reports atomics as allowed (`src/host/transport/p2p/p2p.cpp:62-177`).
- A peer that no transport reaches ends initialization (`src/host/topo/topo.cpp:486-491`). The pinned launch script selects no remote transport, so NVSHMEM's default applies; whether one initializes on this host is not known.
- When every peer has load and store and at least one lacks atomics, the job runs in the mode "load and store" (`set_job_connectivity`, `src/host/init/init.cu:1651-1730`).
- In that mode a put copies into the mapped memory of the peer, and a signal of kind set is a plain store after it (`src/include/non_abi/device/common/nvshmemi_common_device.cuh:491-554`). NVSHMEM's own barrier signals with plain stores and waits on local memory (`src/include/non_abi/device/coll/utils.cuh:41-54`, `coll/barrier.cuh:236-254`).

Inferred: if PCIe peer access between the pairs is available, everything tutorial 03 does and every NVSHMEM operation of tutorial 06 (the put of its inter-node kernel, the barriers of NVSHMEM) needs load and store only, and is expected to work between the pairs through the same mapping as inside a pair, without a NIC. The one operation that needs more is the compare-and-swap of tutorial 06's own barrier kernel, which does not go through NVSHMEM's transport choice: it takes the mapped address (`dl.symm_at`, `CO:161`) and issues the atomic operation itself.

**Replacement batch (decision of 2026-11-21, #478).** `internode-logical-rs06-2x2-002` keeps the harness-built context and sets its barrier constructor argument `is_intra_node=False`. At the pin, this skips the node-team fields and allocation (CO:234–243). The call at T06:344 takes CO:254–255, the global NVSHMEM stream barrier. In the load/store transport mode described above it signals by plain stores. Every successful rank reports `[-1, -1, 2]` from the context (no local rank or size, global barrier). A CAS report uses code 1 and the judge flags it. The variant exercises the peer scatter at T06:279,288–294 and, in the first of two logical-node passes, the inter-node put at T06:364–374. It gives no runtime evidence for the tutorial’s atomic barrier. The observed outputs are recorded below. This is a single-host test.

**Expected and observed outcomes.**

| Request | Expected | Result or diagnostic |
| --- | --- | --- |
| `internode-logical-ag03-2x2-001` | Every test `ok` and `equal`: every rank returns the 64 input bytes. | `runtime_error` in every test with `Peer GPU … is not accessible`: NVSHMEM cannot map across the pairs, and neither request can run with four GPUs. A difference in one segment: the table of programs above says which route delivered it. |
| `internode-logical-rs06-2x2-002` | Exact reduced rows and a global-barrier report on every rank. | Passed on 2026-11-24 (#511). Under both launchers, in both repeats, each of the four ranks returned its exact 256 reduced rows and `[-1, -1, 2]`. |

Tutorial 03 passed with four ranks (#466). In #511, unchanged tutorial 06 completed the peer scatter, inter-node P2P kernel and ring reduction with two logical nodes of two ranks on one host. The harness selected the global NVSHMEM barrier. The tutorial’s atomic barrier and the `putmem_on_stream` path guarded by `has_fullmesh_nvlink()` remain unverified. [Verdict](https://github.com/VeriInfra-Lab/VeriTile-2/issues/511#issuecomment-7124128151) · [Result bundle](https://github.com/VeriInfra-Lab/VeriTile-2/tree/73a5723130934b1e59d93c5750b4d9d0e9cccd7d/results/internode-logical-rs06-2x2-002).

## Affected requests and completion gate

The table records the current disposition of each request.

| Proposed batch | Intended check | Present disposition |
| --- | --- | --- |
| `internode-ag03-single-host-001` | Tutorial 03 1D/2D paths with two local ranks | No manifest of its own: the `one_node` tests of `internode-logical-ag03-001` are this check. |
| `internode-rs06-single-host-001` | Tutorial 06 with two local ranks | No manifest of its own: the `one_node` tests of `internode-logical-rs06-001` are this check. |
| `internode-a2av-single-host-001` | All-to-all core with explicit `local_world_size=2` | Await `gpurun` and a dev-side adapter/manifest; stock test assumes 8. |
| `internode-sp-attn-single-host-001` | Sequence-parallel attention with two local ranks | Await `gpurun` and manifest; remote-node branches remain unexercised. |
| `internode-ag03a-rocm-001` | Unchanged tutorial 03a | Unavailable on H800; requires an AMD environment or an explicitly reviewed port. |
| `internode-logical-env-001` | Two logical nodes come up; one put between two barriers; no kernel | Ran with every test `ok`; bundle not published. Superseded by `internode-logical-env-002`. |
| `internode-logical-env-002` | The same request under a new identifier | Ran on 2026-11-12; judged pass. |
| `internode-logical-ag03-001` | Tutorial 03 under `triton-dist-logical-nodes`, two logical nodes of one rank: the cross-node branch of the 2D all-gather; with the same tests under `triton-dist` as the control | Ran on 2026-11-12 (#434); judged pass on 2026-11-13. Logical-node coverage only. |
| `internode-logical-rs06-001` | Tutorial 06 under the same launcher: `kernel_inter_node_p2p_for_same_local_rank` and the reduction over two nodes; with the same tests under `triton-dist` as the control | Ran on 2026-11-12 (#435); judged pass on 2026-11-13, with `logical_nodes/tutorial_context` failing as predicted. Logical-node coverage only. |
| `internode-logical-ag03-2x2-001` | Tutorial 03, two logical nodes of two ranks: the wait before the intra-node forwarding; with the same tests on one node of four ranks as the control | Judged pass in #466. |
| `internode-logical-rs06-2x2-001` | Tutorial 06, two logical nodes of two ranks: scatter to another local rank, then the P2P kernel; with the same test on one node of four ranks as the control | Withdrawn before announcement. |
| `internode-logical-rs06-2x2-002` | Same test and control, global NVSHMEM barrier. | Ran on 2026-11-24 (#511) and was judged pass. |

Requests requiring two physical nodes remain `skipped_env` under protocol v1. A logical-node run must not be reported as a two-physical-node result; its `meta.json` carries the label `"topology": "logical-nodes"`.

The four-rank tutorial 06 pass in #511 completes the last requested run for #353.
