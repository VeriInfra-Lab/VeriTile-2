[English](GpuInterNodeRuns.md) | [中文](GpuInterNodeRuns.zh.md)

# 跨节点程序在单机上的覆盖范围

Issue：[#353](https://github.com/VeriInfra-Lab/VeriTile-2/issues/353)。检查日期：2026-11-10；逻辑节点 launcher 于 2026-11-12 加入；首个逻辑节点结果以及 tutorial 03 和 06 的请求于 2026-11-12 记录；它们的结果和两个使用四张 GPU 的请求于 2026-11-13 记录。状态：源码检查完成。在这一台主机上启动两个逻辑节点的 launcher 已在 GPU 端运行：`internode-logical-env-002` 于 2026-11-12 返回，判定为通过（两个逻辑节点能够启动，二者之间的一次 put 到达）。针对 tutorial 03 和 06 的请求 `internode-logical-ag03-001` 与 `internode-logical-rs06-001` 已于 2026-11-12 以两个逻辑节点、每节点一个 rank 的方式运行，并于 2026-11-13 判定为通过。Issue 允许的两种结果中，第一种不会成立（见下面的决定）。第二种，即“跨节点代码路径在这一台主机上运行”的检查记录，对启动、对一次 put、以及对 tutorial 03 和 06 中每个逻辑节点一个 rank 就能到达的 `nnodes > 1` 分支成立。每个逻辑节点两个 rank 时，tutorial 03 已通过（#466）。Tutorial 06 等待 NVSHMEM barrier 变体验证（#478）。

**决定（用户，2026-11-12）。** 不再安排第二个物理节点：合作者的集群已不可用。跨节点程序只以这一台主机上的逻辑节点方式测试。主机之间的传输（网卡、RDMA）不在项目范围内：模型里只有 rank 和 scope，没有节点或链路，证明不依赖它。如果逻辑节点无法运行，跨节点代码路径只做证明，并如实报告为未运行。

## 硬件与范围

所检查的主机可见六张 H800 PCIe，计算能力均为 9.0。NVLink 卡对为 0–1、2–3、4–5。每个分布式请求计划只使用两张卡，只有一个例外：`internode-logical-ag03-2x2-001` 和 `internode-logical-rs06-2x2-002` 这两个请求使用四张，即两个 NVLink 卡对（用户决定，2026-11-13）。两个卡对之间只通过 PCIe 相连。本次环境检查使用当时空闲的 4–5 卡对。设备选择不代表资源预留，每次执行前都必须重新检查占用。

下述源码观察均针对 [Triton-distributed `7908e4ea9010bb2238f9f05b28c904fd4b71c60a`](https://github.com/ByteDance-Seed/Triton-distributed/tree/7908e4ea9010bb2238f9f05b28c904fd4b71c60a)。它们说明控制流和配置约束，不代表运行成功或数值正确。

普通单机双进程启动时，`WORLD_SIZE=2`、`LOCAL_WORLD_SIZE=2`、`NNODES=1`。名称带有 `inter_node` 的程序此时可能只执行退化的单节点路径，跳过它原本需要验证的跨节点通信。

## 源码发现

| 程序 | 单机两卡的源码评估 | 未覆盖部分或阻碍 |
| --- | --- | --- |
| [Tutorial 03](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03-inter-node-allgather.py) | 1D all-gather 通过 NVSHMEM 向另一 rank 发送。2D all-gather 接受 `NNODES=1`，执行节点内 peer 分支。尚未实测运行。 | `NNODES=1` 时不覆盖 2D 的相同 local rank、不同节点发送及其接收／转发顺序。 |
| [Tutorial 03a](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/03a-inter-node-allgather.py) | 此固定版本不是 NVIDIA 教程：导入 `pyrocshmem`，使用 ROCSHMEM 设备上下文和信号操作。 | 无法原样在 H800/CUDA 环境执行。需要 AMD/ROCm 主机或单独审阅的 NVIDIA 移植。本次未移植。 |
| [Tutorial 06](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/tutorials/06-inter-node-reduce-scatter.py) | 代码明确支持 `nnodes == 1`，此时返回本地 reduce-scatter 缓冲区。尚未实测运行。 | 只有 `nnodes > 1` 才启动 `kernel_inter_node_p2p_for_same_local_rank`；普通单机双 rank 不会执行该 kernel。 |
| [跨节点 all-to-all kernel](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset_inter_node.py) | 核心上下文可以描述 `world_size=2, local_world_size=2`。现有测试调用 `create_context` 时未覆盖默认的 `local_world_size=8`。 | 现有测试直接使用双 rank 会违反 `world_size % local_world_size == 0`。开发端适配器必须显式传入 2。只有一个逻辑节点时跳过异节点接收等待分支。本次未修改测试或 kernel。 |
| [跨节点序列并行 all-gather attention kernel](https://github.com/ByteDance-Seed/Triton-distributed/blob/7908e4ea9010bb2238f9f05b28c904fd4b71c60a/python/triton_dist/kernels/nvidia/sp_ag_attention_inter_node.py) | 现有测试由 `WORLD_SIZE / LOCAL_WORLD_SIZE` 得到 `NNODES`，并将二者传入上下文。单机双 rank 配置执行节点内 all-gather 路径。尚未实测运行。 | `NNODES=1` 时不覆盖异节点 put 及跨节点接收／转发同步。 |

## 启动约束

固定版本的 `scripts/launch.sh` 识别 `--nproc_per_node=2`（必须带 `=`）。默认分支通过 `nvidia-smi` 统计物理设备，因此在这台六卡机器上仅设置 `CUDA_VISIBLE_DEVICES` 不够。后续开发端请求必须明确选择两张可见卡和两个进程。

不能只修改 `LOCAL_WORLD_SIZE` 来伪造拓扑：初始化会将 `LOCAL_RANK` 映射到 CUDA 设备，对称 peer 缓冲区的构造也依赖节点内分组。在一台物理主机上运行两个逻辑节点，需要明确的 launcher 与 batch 描述；下一节给出二者。即使它执行了异节点源码分支，也不能证明跨主机网卡、RDMA/IBGDA、隔离、延迟或故障行为。

## 单机上的逻辑节点

2026-11-12 加入。本节内容中，launcher 以及两个逻辑节点之间的一次 put 已在 GPU 上运行（`internode-logical-env-002`，见小节“首个请求及其结果”）；尚无教程 kernel 在该 launcher 下运行。launcher 还在没有 GPU 的开发机上用固定脚本的替身做了测试。凡涉及 torchrun、NVSHMEM 或 NCCL 的陈述，都是从所引源码读到的，或由其推断的，并逐条注明是哪一种；小节“只有 GPU 端运行才能确定的事项”说明其中哪些已被那次运行确认。

### Launcher

`gpurun` 增加了第二个 `dist` launcher：`triton-dist-logical-nodes`，以及测试字段 `logical_nodes`（见 [GpuExchangeProtocol.md](GpuExchangeProtocol.md) 第 5、6、9 节）。它在同一台主机上为每个逻辑节点启动一次固定版本的 `scripts/launch.sh`，并通过该脚本本来就读取的多节点变量来驱动它。以 `ranks` 为 2、`logical_nodes` 为 2 为例：

| 传给逻辑节点 n（0 或 1）的设置 | 固定脚本如何使用（读自固定版本的 `scripts/launch.sh`） |
| --- | --- |
| `ARNOLD_WORKER_NUM=2`、`ARNOLD_ID=n` | 向 torchrun 传入 `--nnodes=2 --node_rank=n`。 |
| `--nproc_per_node=1` | 每个节点一个 rank。不带该参数时脚本用 `nvidia-smi` 统计物理 GPU。 |
| `ARNOLD_WORKER_0_HOST=127.0.0.1` | 传入 `--rdzv_endpoint=127.0.0.1:<port>`。该地址是 launcher 中的常量。端口沿用脚本的取值：`23456`，或操作员设置的 `ARNOLD_WORKER_0_PORT`。 |
| `CUDA_VISIBLE_DEVICES=` 操作员列表中的第 n 项 | 脚本不读取；由 torchrun 和 rank 进程继承。 |

其余设置保持脚本原样，包括 NVSHMEM 的设置：`NVSHMEM_BOOTSTRAP=UID`、bootstrap 网络接口、对称堆大小、`NVSHMEM_DISABLE_CUDA_VMM=1`。launcher 不需要接口名：两个逻辑节点都在同一台主机上，操作员已为 `dist` 批次选定了这台主机的接口。请求中不出现主机名、接口名或地址。

按 GPU 端报告的 PyTorch 版本（2.8.0）的 torchrun 源码（`torch/distributed/elastic/agent/server/local_elastic_agent.py`，以及 `api.py` 中的 `_assign_worker_ranks`），每个 rank 预期看到：`WORLD_SIZE=2`、`LOCAL_WORLD_SIZE=1`、`LOCAL_RANK=0`；节点 0 上 `RANK` 为 0，节点 1 上为 1。固定版本的 `initialize_distributed` 随后在两个 rank 中都调用 `torch.cuda.set_device(0)`，而设备 0 在两个 rank 中是不同的物理 GPU：即该 rank 在 launcher `triton-dist` 下使用的那张卡。程序由此得到 `nnodes = WORLD_SIZE // LOCAL_WORLD_SIZE = 2`。如果某个 rank 的 `LOCAL_WORLD_SIZE` 不等于 `ranks / logical_nodes`，`gpurun` 在调用 harness 之前就终止该 rank。

设计选择。另一种方案是自己写 launcher：自行启动每个 rank，并设置 `RANK`、`LOCAL_RANK`、`WORLD_SIZE`、`LOCAL_WORLD_SIZE`、torch 的 rendezvous 变量和 NVSHMEM 设置。最终选择为每个逻辑节点启动一次固定脚本，因为这样保留固定的 NVSHMEM 设置和 torchrun，新增代码约二十行。它依赖：

1. 脚本的多节点变量保持在固定版本中读到的含义；
2. torchrun 的静态 rendezvous 接受同一主机上的两个 agent：node rank 为 0 的 agent 在该端点上提供 store，另一个 agent 连接它（读自 `torch/distributed/elastic/rendezvous/static_tcp_rendezvous.py`；未运行）；
3. torchrun 把自身的环境变量（包括 `CUDA_VISIBLE_DEVICES`）传给每个 rank（读自 `torch/distributed/elastic/multiprocessing/subprocess_handler/subprocess_handler.py`）；
4. NCCL 和 NVSHMEM 能够访问本进程不可见的 GPU（见下一小节）。

每个逻辑节点只能看到自己的 GPU，与真实集群中的节点一致。如果 GPU 运行表明第 4 项不成立，退路是让每个逻辑节点都能看到全部 GPU，并把本节点的 GPU 排在最前：这样 NVSHMEM 和 NCCL 看到的 peer 与 `triton-dist` 下相同，但统计可见设备数的程序会看到比真实节点更多的设备。该退路尚未实现。

### 两张 GPU 之间预期使用的传输

本小节是根据源码得出的预期，不是观测结果。库源码在这里只用于预测运行能否启动，不定义任何语义。

来源（均于 2026-11-12 在 github.com 上阅读）：

- NVSHMEM：[`NVIDIA/nvshmem` 的 tag `v3.6.5-0`](https://github.com/NVIDIA/nvshmem/tree/6e53a40d9db16df170b3b0057e94c340d72f77eb)，commit `6e53a40d9db16df170b3b0057e94c340d72f77eb`。固定版本 Triton-distributed 的 `python/setup.py` 要求 `nvidia-nvshmem-cu12==3.6.5`。
- NCCL：[`NVIDIA/nccl` 的 tag `v2.27.3-1`](https://github.com/NVIDIA/nccl/tree/72d2432094d6ae36abd6e511c3a16a2d052dbf94)，commit `72d2432094d6ae36abd6e511c3a16a2d052dbf94`。PyTorch 2.8.0 对 CUDA 12.6 要求 `nvidia-nccl-cu12==2.27.3`（`.github/scripts/generate_binary_build_matrix.py`）。
- PyTorch：[`pytorch/pytorch` 的 tag `v2.8.0`](https://github.com/pytorch/pytorch/tree/ba56102387ef21a3b04b357e5b183d48f0afefc7)，commit `ba56102387ef21a3b04b357e5b183d48f0afefc7`。

GPU 端安装的版本，据 `internode-logical-env-002` 的 `env.json`：PyTorch `2.8.0+cu126`、NVSHMEM 库 `3.6.5`、NVSHMEM 绑定 `0.3.0`、Triton `3.7.1`。未确认：NCCL 的版本，`env.json` 不报告它。

从源码读到：

- NVSHMEM 用 `gethostname()` 的哈希来标识主机（`src/host/util/util.cpp`，`nvshmemu_getHostHash`）。launcher 设置的内容都不参与该哈希。
- 它的 P2P 传输（`src/host/transport/p2p/p2p.cpp`，`nvshmemt_p2p_can_reach_peer`）不访问主机哈希不同的 peer。对哈希相同的 peer，它在本进程可见的设备中查找 peer 的 GPU。找到时，询问 `cudaDeviceCanAccessPeer`。找不到时（源码将其归因于 `CUDA_VISIBLE_DEVICES`），若 CUDA 驱动为 12 或更高版本，或堆不是 VMM 堆，则向 NVML 查询两个设备之间的 P2P 状态，读写均允许时授予映射。否则它发出警告，说明改用网络传输。
- 任何传输都无法到达的 peer 会使初始化以 `Peer GPU … is not accessible` 结束（`src/host/topo/topo.cpp`，`nvshmemi_build_transport_map`）。
- `initialize_distributed` 用 NCCL 建立进程组；NCCL 在主机哈希相同时把两个 rank 视为本地；对本进程不可见的 peer 设备，其 P2P 检查处的注释为 `CUDA 10.1 and later can use P2P with invisible devices`（`src/transport/p2p.cc`）。

推断：两个逻辑节点的主机哈希相同，因此预期 NVSHMEM 在两张 GPU 之间使用 P2P 传输，也就是普通单节点运行所用的、对 peer 对称堆的映射，经由该卡对的 NVLink。由于每个逻辑节点隐藏了对方的 GPU，这一结果经由 NVML 分支得到。预期没有网卡，也没有远程传输（IBRC、UCX、IBGDA、libfabric）承载数据。

### 逻辑节点运行覆盖什么

以下是对固定版本源码的阅读结果，针对两个逻辑节点、每节点一个本地 rank（`WORLD_SIZE=2`、`LOCAL_WORLD_SIZE=1`、`nnodes=2`）：

| 程序 | 两个逻辑节点、每节点一个 rank 时到达的部分 | 仍未到达的部分 |
| --- | --- | --- |
| Tutorial 03 | `NNODES=2`。在 `all_gather_push_2d_kernel` 中，每个 program 都满足 `peer_local_rank == local_rank`：对应另一 rank 的 program 执行跨节点的 `putmem_signal_nbi_block`，对应自身 rank 的 program 等待 peer 的信号。 | 节点内分支，包括先等待来自另一节点的分段再转发。它需要本地 rank 不同的 peer：两个节点各两个本地 rank，共四张 GPU。 |
| Tutorial 06 | `nnodes=2`。启动 `kernel_inter_node_p2p_for_same_local_rank`（`n = 0` 时），结果取自 P2P 缓冲区，`ring_reduce` 在两个节点上进行。这需要一个上下文，而教程自己的构造函数在节点 0 之外给不出它（见小节“教程请求”）。 | 向另一本地 rank 的 `intra_node_scatter`：只有一个本地 rank 时它复制到该 rank 自己的缓冲区。 |
| 跨节点 all-to-all kernel | 显式传入 `local_world_size=1` 时 `nnodes=2`，因此 pull 循环会遇到 `src_node != node_id` 并等待另一节点的信号。只阅读了这几行；没有进一步追踪该 kernel。 | 接收节点上不同本地 rank 之间的转移。 |
| 跨节点序列并行 all-gather attention kernel | 其 push kernel 与 tutorial 03 的 2D kernel 结构相同：向相同本地 rank 的跨节点 put。只阅读了这几行。 | 节点内转发分支，与 tutorial 03 相同。 |

该 launcher 也能把四个 rank 启动为两个逻辑节点、每节点两个 rank（`ranks` 为 4、`logical_nodes` 为 2；已用替身测试），这会到达转发分支。这需要在一个请求中使用四张 GPU；这台主机的规则是两张，用户已为每个教程各一个请求批准了例外。小节“教程请求”按行列出 tutorial 03 和 06 的分支，以及阅读过程中的发现；其后的小节是两个四 rank 的请求。

### 它不覆盖什么

- 网卡，以及 RDMA 或 IBGDA 传输：预期数据在一台主机内通过 GPU 点对点映射传递。
- 跨主机的 NVSHMEM bootstrap、NCCL 和 torchrun rendezvous：三者都在一台主机内连接。
- 主机之间的隔离：逻辑节点共用操作系统、主机名、文件系统（包括 Triton 缓存目录）和 CPU 内存。
- NVSHMEM 眼中的节点边界。NVSHMEM 把主机名哈希相同的 rank 放进同一个节点 team（`init_team_node`，tag `v3.6.5-0` 的 `src/host/team/team_internal.cpp:1106-1130`；2026-11-12 阅读，未运行），因此两个逻辑节点是同一个 NVSHMEM 节点。不读 `LOCAL_WORLD_SIZE`、而向 NVSHMEM 询问哪些 rank 与自己同节点的代码，看到的是一个包含全部 rank 的节点。Tutorial 06 的节点内 barrier 就是这样的代码（见小节“教程请求”）。
- 节点间网络的延迟、带宽和时序。
- 故障：节点丢失、链路丢失、网络分区。

因此，逻辑节点结果说明的是 `nnodes > 1` 分支的控制流和 rank 运算，以及发往另一节点 rank 的数据能够到达，所用传输与单节点运行相同。它是关于程序文本的证据，不是关于主机间通信的证据。`gpurun` 会给它打标签：`meta.json` 中有 `"topology": "logical-nodes"` 以及 `logical_nodes` 和 `local_ranks`；`requires.nodes` 和 `GPURUN_NODES` 保持为 1；如果批次要求多于一个物理节点，其中的逻辑节点测试返回 `skipped_env`。

### 只有 GPU 端运行才能确定的事项

前七项中每一项之后是它在 `internode-logical-env-002`（见下一小节）之后的状态，第 7 至 10 项之后是它在两个每逻辑节点一个 rank 的教程请求之后的状态。“已确定”指在所指的批次中观察到：两次重复，一对 GPU。

1. 同一主机上的两个 torchrun agent 能否在回环端点上汇合，固定端口 `23456` 是否空闲：共享主机上的其他作业，或上一次重复留下的 store，可能占用它。**对那次运行已确定：**两次重复中两个 agent 都在回环地址的端口 `23456` 上汇合，每个 rank 都启动了。端口是否空闲仍是每次运行各自的问题。
2. 每个 rank 是否得到预期的 `RANK`、`LOCAL_RANK`、`WORLD_SIZE` 和 `LOCAL_WORLD_SIZE`。**已确定：**各 rank 报告了预期的值（见下一小节的表）。
3. NCCL 能否在各自只能看到一张 GPU 的两个 rank 之间建立进程组。**已确定：**`initialize_distributed` 在两个 rank 中都返回了；它在全部 rank 上建立 NCCL 组并在其上执行一次 barrier（固定版本的 `python/triton_dist/utils.py:355-356`）。
4. NVSHMEM 的 UID bootstrap 能否跨两个 launcher 组完成。按源码，它只看到 `initialize_distributed` 传入的唯一标识、rank 和 rank 总数，看不到分组。**已确定：**NVSHMEM 在两个 rank 中都完成了初始化，其后的 barrier 和 put 也都完成。
5. NVSHMEM 能否通过 NVML 访问被隐藏的 peer GPU 并映射其堆，还是以 `Peer GPU … is not accessible` 终止；以及安装的 NVSHMEM 库是哪个版本。**结果已确定：**初始化没有终止，put 到达，日志中既没有该消息，也没有关于网络传输的警告。日志中看不出源码的哪个分支授予了映射。安装的库是 `3.6.5`（`env.json`）。
6. 发往另一逻辑节点 rank 的 put 是否到达，以及已安装绑定中的 `nvshmem.core.put` 是否接受 harness 的调用。**已确定：**每个 rank 都收到了另一 rank 的四个值。未确定，且那个批次没有涉及：固定版本中唯一的主机端 put，它走底层绑定，即 `python/triton_dist/kernels/nvidia/reduce_scatter.py` 中的 `pynvshmem.putmem_on_stream`（`reduce_scatter_for_each_node_ring`，位于 `nnodes > 1` 之下），调用时传入四个参数，而 NVSHMEM tag `v3.6.5-0` 的绑定声明了五个参数，最后一个是 stream（`nvshmem4py/nvshmem/bindings/nvshmem.pyx:1615`）。Tutorial 06 到达不了这个调用（见小节“教程请求”），所以它的请求也不会确定这一点。
7. 两个逻辑节点同时向同一个 Triton 缓存目录编译时是否互相干扰。**对这些运行已确定：**环境批次没有编译任何 kernel；在两个教程请求中，每个 `logical_nodes` 测试的第一次重复里两个逻辑节点同时编译相同的 kernel，每个这样的测试都以 `ok` 结束并返回预期张量。这是两个进程；四个进程尚未观察。

随教程请求新增：

8. Tutorial 03 和 06 的 kernel 在已安装的环境中能否编译并运行。`one_node` 对照测试在逻辑节点之外回答这一点。**已确定：**tutorial 03 的两个 kernel 以及 tutorial 06 启动的 kernel 在两个 launcher 下都运行了。
9. Triton 的 JIT 能否从一个只含该文件各项定义的模块中编译 tutorial 03 的 kernel；harness 正是这样避免运行教程的程序。开发机上只测试到 `inspect.getsourcelines`（JIT 用它读取 kernel）返回该文件的文本为止。**已确定：**`internode-logical-ag03-001` 的四个测试都以这种方式编译了各自的 kernel。
10. NVSHMEM 的节点 team 在逻辑节点下报告什么（按源码预期：这台主机上的全部 rank），以及使用它的 tutorial 06 节点内 barrier 能否跨两个逻辑节点完成。**已确定：**在两个 launcher 下，rank r 都报告自己是 2 个 rank 的节点 team 中的本地 rank r，原生原子操作为 1，barrier 完成。

随四 rank 的请求（小节“两个逻辑节点、每节点两个 rank 的请求”）新增，均未确定：

11. NVSHMEM 能否到达另一个 NVLink 卡对上的 GPU 并映射其内存：该 GPU 可见时（`one_node`）通过 `cudaDeviceCanAccessPeer`，被隐藏时（`logical_nodes`）通过 NVML 对两个设备给出的状态。如果不能，两个请求的每个测试都会在初始化时以 `Peer GPU … is not accessible` 停止。
12. NCCL 能否在四个 rank 上建立进程组，包括一个 launcher 组四个 rank 以及两个组各两个 rank 两种情况。
13. 不同卡对的两张 GPU 对原生原子操作报告什么。硬件描述意味着是 0；这里读过的任何材料都没有这样写。`internode-logical-rs06-2x2-002` 的每个 rank 都会打印它可见设备中每一对的回答。
14. Tutorial 06 的 barrier 所用的 compare-and-swap kernel，在通过一条报告没有原生原子操作的链路到达的内存上会怎样：完成、挂起，或者 GPU 报错。这里读过的任何文档都没有说明是哪一种。
15. 主机侧向另一卡对上某个 rank 的张量做的复制是否到达（tutorial 06 请求的 `one_node/harness_context`：每个 rank 向三个 rank 做 scatter，其中两个在另一卡对上）。
16. Tutorial 03 的“先接收再转发”分支，以及 tutorial 06 的 scatter 接跨节点 put，是否返回预期张量。

### 首个请求及其结果

`internode-logical-env-001`（`experiments/interp_gpu/batches/internode-logical-env-001/`，harness 为 `experiments/interp_gpu/smoke/dist_logical_nodes.py`）在不使用教程 kernel 的情况下处理第 1 至 6 项。每个 rank 通过固定版本的 `initialize_distributed` 初始化；以张量形式报告自己的 rank、world size、`LOCAL_WORLD_SIZE`、推导出的节点数、`LOCAL_RANK` 和 CUDA 设备索引；打印设备名称；在两次 barrier 之间向另一 rank 的对称内存 put 四个值；然后结束。第一次 barrier 用来保证接收方初始化缓冲区之前不会有 put 到达。

该批次有两个使用同一 harness 的测试：`one_node/put_barrier` 使用 `triton-dist`，作为对照；`logical_nodes/put_barrier` 使用新的 launcher。这样可以把 harness 自身的失败与逻辑节点的失败区分开。开发端的预期：对照测试中 `LOCAL_WORLD_SIZE` 为 2，一个节点，设备索引等于 rank；逻辑节点测试中 `LOCAL_WORLD_SIZE` 为 1，两个节点，两个 rank 的设备索引均为 0；两个测试中，每个 rank 都收到 100 加上另一 rank 的编号。

结果。`internode-logical-env-001` 已在 GPU 端运行，每个测试均为 `ok`，但其结果包没有发布：launcher 的日志中有回环地址，而当时公开结果的规则不允许日志中出现地址。`gpurun` 现在把该地址写成 `<loopback>`，同一请求于 2026-11-12 以 `internode-logical-env-002` 再次运行（[issue #430](https://github.com/VeriInfra-Lab/VeriTile-2/issues/430)；请求 commit `ad26d295f4f8737ab82df8312a7eed21bbc4366c`；结果包为分支 `gpu-results` 的 commit `3ff8914868fa562c7dff6caac9344627732c4ce4` 中的 `results/internode-logical-env-002/`）。两个测试在两次重复中均为 `ok`，两个 rank 均为 `ok`，使用 NVLink 卡对 4–5。开发端解码的结果，两次重复相同：

| 测试 | Rank | `topology`（rank、world size、`LOCAL_WORLD_SIZE`、节点数、`LOCAL_RANK`、设备索引） | `received` |
| --- | --- | --- | --- |
| `one_node/put_barrier` | 0 | 0, 2, 2, 1, 0, 0 | 四个 101 |
| `one_node/put_barrier` | 1 | 1, 2, 2, 1, 1, 1 | 四个 100 |
| `logical_nodes/put_barrier` | 0 | 0, 2, 1, 2, 0, 0 | 四个 101 |
| `logical_nodes/put_barrier` | 1 | 1, 2, 1, 2, 0, 0 | 四个 100 |

每个值都与预期一致，因此该批次判定为通过：两个各含一个 rank 的逻辑节点经由固定的 launcher 在这一台主机上启动，每个 rank 只看到自己的 GPU，运行时推导出两个节点，发往另一逻辑节点上 rank 的 put 到达。上一小节说明这确定了哪些事项。

### 教程请求

写于 2026-11-12；两者当天都在 GPU 端运行，并于 2026-11-13 判定（见本小节末尾的“结果”）。`internode-logical-ag03-001` 和 `internode-logical-rs06-001`（位于 `experiments/interp_gpu/batches/` 下）用 2 个 rank、在固定的小输入上调用 tutorial 03 和 06 的函数。`logical_nodes/` 下的每个测试（launcher `triton-dist-logical-nodes`，两个逻辑节点、每节点一个 rank）在 `one_node/` 下都有一个对照（launcher `triton-dist`），harness、输入和输出相同，这样可以把教程的失败与逻辑节点的失败区分开。每个 rank 返回自己的结果张量以及环境批次中的 `topology` 值。harness 是 `experiments/interp_gpu/internode_logical/harness.py`。同目录的 `judge.py` 用 Python 标准库从重新生成的输入计算预期张量，并按测试、rank 和输出逐项打印 `equal` 或 `different`；`test_internode_logical.py` 在没有 GPU 的情况下测试二者。没有修改或复制任何教程文件：harness 从构建该环境所用的 checkout 中读取它。这两个批次提交时没有 issue 也没有标签，之后由协调者公告。

`T03:n`、`T06:n`、`RS:n`、`CO:n` 和 `UT:n` 分别指固定版本中 `tutorials/03-inter-node-allgather.py`、`tutorials/06-inter-node-reduce-scatter.py`、`python/triton_dist/kernels/nvidia/reduce_scatter.py`、`python/triton_dist/kernels/nvidia/common_ops.py` 和 `python/triton_dist/utils.py` 的行，与 [dist/EventControlFlow.md](dist/EventControlFlow.md) 的用法相同。本小节“结果”之前的全部内容都是 2026-11-12 从源码读到的，或由其推断的，并且写于运行之前。

**Tutorial 03，`internode-logical-ag03-001`。** 四个测试：kernel `push_1d` 和 `push_2d`，各在两个 launcher 下。输入：64 字节，每个 rank 相同；rank r 拥有第 32r 至 32r + 31 字节。一个 rank 的缓冲区起初是自己的分段，其余位置为 sentinel；一次 kernel 调用之后作为 `gathered` 返回。预期：每个测试为 `ok`，每个 rank 的 `gathered` 等于 64 个输入字节。

| Kernel 文本 | `one_node`（一个节点、两个 rank） | `logical_nodes`（两个节点、各一个 rank） | 留给两个节点、各两个 rank 的部分 |
| --- | --- | --- | --- |
| `all_gather_push_1d_kernel`（`T03:62-95`）；其中没有按节点数的分支 | 向另一 rank 的带信号 put（`T03:85-95`），以及对其信号的等待（`T03:72-76`）。 | 相同。 | 无。 |
| `all_gather_push_2d_kernel`，本地 rank 相同、rank 不同的 program（`T03:135-147`）：跨节点的 `putmem_signal_nbi_block` | 未到达。 | 到达：每个 program 都满足 `peer_local_rank == local_rank`，对应另一 rank 的 program 把本 rank 的分段 put 到另一节点。 | 无。 |
| 同一 kernel，对应本 rank 自身的 program（`T03:148-155`）：等待每个 peer 的信号 | 到达。 | 到达。 | 无。 |
| 同一 kernel，本地 rank 不同的 program（`T03:156-177`）：节点内的 `putmem_signal_block` | 到达，但没有 `T03:160-167` 的等待，因为 `peer_node_id == node_id`。 | 未到达。 | 在节点内转发之前对来自另一节点的分段的等待（`T03:160-167`）。 |

阅读过程中的发现：

- **该教程在 import 时运行它的整个程序。** 文件没有 `__main__` 保护：`T03:256-299` 启动运行时、生成随机数据、对两个 kernel 计时并停止运行时。因此 harness 只执行该文件顶层的 import、类和函数。它过滤语法树，并以该文件的名字编译，使 Triton 的 JIT 仍然在原来的行上读到未改动的 kernel 文本。harness 自己充当围绕这些定义的程序：每个测试一个 64 字节的缓冲区、一次 kernel 调用，而教程使用双缓冲区和一个计时循环。
- **信号张量：`dist/EventControlFlow.md` 第 8 节第 5 条观察的读法已由源码确认。** `T03:276-278` 以形状 `(1, )` 创建每个信号张量，即一个 8 字节的字（`UT:572`）；`T03:103` 和 `T03:185` 把其中一个作为 `symm_flag` 传入。1D kernel 对每个小于 `WORLD_SIZE` 且不等于本 rank 的 `peer` 等待 `symm_flag + peer`（`T03:68-76`），并对 `symm_flag + segment` 发信号，其中 `segment = rank`（`T03:81`、`T03:91`）。2D kernel 在 `T03:138-143`、`T03:149-154`、`T03:158-163` 和 `T03:173` 做同样的事。两个 rank 时，rank 1 设置 rank 0 上该张量的第 1 个字，rank 0 等待这个字：比教程分配的多出一个字。因此只要 `WORLD_SIZE > 1`，教程的程序就访问张量之外的内存，一个节点时如此，两个节点时也如此；分配器是否恰好不使用那个字，未知。本批次不运行那个程序。harness 为每个信号张量分配 `ranks` 个字，并明确说明这一点。没有选择按原样运行教程，是因为没有任何结果能显示这个缺陷：通过并不能否定它，而挂起、错误的字节或分配器报错都可能另有原因。

**Tutorial 06，`internode-logical-rs06-001`。** 文件有 `__main__` 保护（`T06:448`），整体 import。输入：每个 rank 一个 512 乘 128 的矩阵，元素为 -100 到 100 之间的整数，转换为 bfloat16，即教程的 dtype（`T06:458`）。按教程的 `__main__` 的方式调用 `reduce_scatter_2d_op`（`T06:410-433`），前后是相同的两次 barrier（`T06:474-479`），其返回值作为 `reduced` 返回。rank r 的预期：两个矩阵之和的第 256r 至 256r + 255 行。每个和都是绝对值不超过 200 的整数，bfloat16 可以精确表示，因此比较不带容差。该形状是使 `kernel_ring_reduce_tma` 的每个 tile（256 行乘 64 或 128 列，`RS:749-775`）都落在其张量之内的最小形状，与教程自己的 8192 乘 16384 情况相同；更小的矩阵还会顺带测试 tile 跨越张量边界时的行为，而那不是这里要测的。

| 文本 | `one_node`（一个节点、两个 rank） | `logical_nodes`（两个节点、各一个 rank） | 留给两个节点、各两个 rank 的部分 |
| --- | --- | --- | --- |
| 对节点的循环（`T06:314`） | 一轮：本节点。 | 两轮：先另一节点，再本节点。 | 无。 |
| `intra_node_scatter`（`T06:264-294`），主机端复制 | 复制到另一 rank 的缓冲区。 | 复制到本 rank 自己的缓冲区（`remote_local_rank == local_rank`）。 | 两轮中各有一次向另一本地 rank 的复制。 |
| `barrier_all_on_stream`（`T06:344`） | 节点内 barrier kernel，跨两个 rank。 | 同一 kernel，预期跨两个 rank，而真实的单 rank 节点只会跨一个（见下）。 | 无。 |
| 每个节点的 `ring_reduce`（`T06:349-354`） | 两个块求和。 | 一个块的复制（`num_splits` 为 1）。 | 每轮两个块求和。 |
| `nnodes > 1` 之下（`T06:357`），最后一轮（`T06:358-363`）：把本 rank 自己的结果复制到 P2P 缓冲区 | 未到达。 | 到达，第二轮。 | 无。 |
| `nnodes > 1` 之下，其余各轮（`T06:364-374`）：`kernel_inter_node_p2p_for_same_local_rank`，向另一节点上相同本地 rank 的一次 `putmem_block`（`T06:256-261`） | 未到达。 | 到达，第一轮。 | 无。 |
| 返回值（`T06:377-379`） | 每节点缓冲区。 | P2P 缓冲区。 | 无。 |
| 对节点的 `ring_reduce`（`T06:406`） | 一个块的复制（`num_splits = nnodes = 1`）。 | 两个块求和，其中一个收自另一节点。 | 无。 |

四个测试：`tutorial_context` 和 `harness_context`，各在两个 launcher 下。阅读过程中的发现：

- **教程的上下文构造函数在节点 0 之外会失败：一个预测的失败。** `create_reduce_scater_2d_ctx` 通过 `nvshmem_create_tensors(..., rank, local_world_size)` 得到信号张量，这是一个列表，调用者所在节点的每个 rank 对应一项（`UT:257-272`），随后用全局 rank 取 `signal_bufs[rank]`（`T06:199-202`）。在节点 0 的 rank 中，取到的是该 rank 自己的张量。在其他任何 rank 中，下标超出列表末尾：`IndexError: list index out of range`，此时还没有启动任何 kernel。因此按原样的 tutorial 06 无法在多于一个节点上运行，无论逻辑节点还是物理节点。本请求既暴露这一点，也绕开它，分别放在不同的测试中：
  - `*/tutorial_context` 按教程 `__main__` 的方式调用教程的构造函数（`T06:460-466`）。在 `one_node` 下预期能工作。在 `logical_nodes` 下预期 rank 1 抛出该 `IndexError`，随后 rank 0 预期在 `T06:205` 的 barrier 中等待它，直到该测试的超时 240 秒。`logical_nodes/tutorial_context` 的预期状态是 `timeout` 或 `runtime_error`，其中 rank 1 为 `runtime_error`，`stderr.log` 中有该 `IndexError`。judge 把这种情况称为 `failed as predicted`，其他情况称为 `prediction not met`。这个失败正是该测试想要的结果；批次的 notes 向 GPU 端说明了这一点。
  - `*/harness_context` 在 harness 中构造同样的 `ReduceScatter2DContext`，分配和取值与 `T06:188-229` 相同，只是那一个下标在节点内取（`rank % local_world_size`）。其后的一切都是教程的代码。`logical_nodes/harness_context` 就是到达表中 `nnodes > 1` 分支的那个测试。
- **到达不了 `putmem_on_stream`。** Tutorial 06 定义了自己的 `reduce_scatter_for_each_node` 和 `reduce_scatter_multi_node`（`T06:297`、`T06:382`），从库文件中只 import 了 `ring_reduce`（`T06:49`）。传入四个参数的 `pynvshmem.putmem_on_stream` 调用位于 `reduce_scatter_for_each_node_ring`（`RS:538-543`）。它唯一的调用者是库中的 `reduce_scatter_multi_node`，在 `has_fullmesh_nvlink()` 为假时调用（`RS:807-808`）；tutorial 08 会到达该函数，tutorial 06 不会。因此预期本批次不会出现由该调用引起的 `runtime_error`，本文的所有批次也都不会执行到该调用。
- **节点内 barrier 看不到逻辑节点。** 上下文持有 `BarrierAllContext(True)`（`T06:223`），它的本地 rank 和节点大小取自 NVSHMEM 的节点 team（`CO:238-240`），而不是 `LOCAL_WORLD_SIZE`。两个逻辑节点是同一个 NVSHMEM 节点（见小节“它不覆盖什么”）。因此在 `logical_nodes` 下，预期 `T06:344` 的 barrier 跨两个 rank 执行。两个 rank 调用它的次数相同，每轮一次，所以预期它能完成：对单 rank 节点而言，它同步的范围比文本的意图更大，而不是更小。每个 rank 在 `barrier` 中返回该 barrier 的本地 rank 和节点大小；两个 launcher 下的预期都是 r 和 2。
- **逻辑节点下原生原子操作是被假定的。** 当 `supports_p2p_native_atomic()` 成立时，`barrier_all_on_stream` 启动 compare-and-swap kernel（`CO:257-258`）。进程只看到一张 GPU 时，该函数不询问驱动就返回真（`UT:536-538`），单 rank 逻辑节点的每个 rank 都是这种情况；在 `one_node` 下它向驱动询问这对 GPU（`UT:544-547`）。该 kernel 的 docstring 禁止在 GPU 之间的链路没有原子操作时使用它（`CO:155-157`）。`barrier` 的第三个值是该函数的回答：在 NVLink 卡对上，两个 launcher 下预期都是 1（由该 docstring 推断，它把 PCIe 称为没有原子操作的情况）。如果 `one_node` 下为 0，就意味着 `logical_nodes` 测试在一对报告不支持原子操作的 GPU 上使用了原子操作。该请求应在 NVLink 卡对上运行，与环境批次相同。

**结果。** 两个请求都于 2026-11-12 在 GPU 端运行一次，请求 commit 为 `4e9a91a52577f00649442e2454b8bb51cbab42a7`，使用 NVLink 卡对 4–5；开发端于 2026-11-13 用 `judge.py` 判定，它对两个结果包都以 0 退出（为撰写本文于 2026-11-13 重新执行过）。

| 请求 | Issue | `gpu-results` 上的结果包 | 各测试的状态 | 判定 |
| --- | --- | --- | --- | --- |
| `internode-logical-ag03-001` | [#434](https://github.com/VeriInfra-Lab/VeriTile-2/issues/434) | `results/internode-logical-ag03-001/`，commit `c8bc3631b45c9b2071ddf52e0b9de0394d4c6425` | 四个测试均为 `ok`，各两次重复，两个 rank 均为 `ok` | 通过：每个测试中两个 rank 在两次重复里都返回预期的 `topology` 和 64 个输入字节。 |
| `internode-logical-rs06-001` | [#435](https://github.com/VeriInfra-Lab/VeriTile-2/issues/435) | `results/internode-logical-rs06-001/`，commit `326fa57e4a063af67062a4b3cf48865824b3609c` | 三个测试为 `ok`，各两次重复；`logical_nodes/tutorial_context` 在 239.9 秒后 `timeout`，rank 0 没有状态，rank 1 为 `runtime_error` | 通过，并观察到预测的失败：三个测试在两个 rank、两次重复中都返回预期的 `topology`、`barrier` 和 `reduced`（精确，无容差）；第四个为 `failed as predicted`。 |

这些结果确立的内容，每一条都只针对一次运行、两次重复、一个卡对：

- Tutorial 03：每个逻辑节点一个 rank 时，2D kernel 执行了它的跨节点 put 和等待（`T03:135-155`），之后每个 rank 都持有完整的输入。kernel 未改动；信号张量是 harness 的，每个 rank 一个字。“先接收再转发”分支（`T03:156-177`，含 `T03:160-167` 的等待）没有运行。
- Tutorial 06 按原样无法在多于一个节点上启动：rank 1 在任何 kernel 之前于 `T06:202` 抛出 `IndexError: list index out of range`，rank 0 一直等到超时。这是观察到的，不只是读到的。
- Tutorial 06 使用 harness 构建的上下文：跨节点 P2P kernel（`T06:364-374`）和两个节点上的归约（`T06:406`）在两个逻辑节点上运行，每个 rank 返回精确和中属于它的行。**决定（用户，2026-11-13）：**这次运行算作 tutorial 06 在逻辑节点上的运行；偏离之处（主机侧的一个下标，kernel 未改动）保留记录。
- 在两个 launcher 下，每个 rank 都报告自己是 2 个 rank 的节点 team 中的本地 rank r：NVSHMEM 的节点 team 跨越两个逻辑节点，与读到的一致。两个 launcher 都报告原生原子操作为 1；在 `one_node` 下这是驱动对卡对 4–5 的回答。
- `nnodes > 1` 下向另一本地 rank 的 scatter 没有运行：每节点一个 rank 时，`intra_node_scatter` 复制到该 rank 自己的缓冲区。

**决定（用户，2026-11-13）。** 在固定版本的教程中发现的缺陷现在不向上游报告。它们先被收集，经确认的在项目接近结束时报告。

### 两个逻辑节点、每节点两个 rank 的请求

以下分析记录 2026-11-13 的原始请求。Tutorial 03 随后通过（#466）。用户于 2026-11-21 在公告前撤回了原 tutorial 06 请求。下文的替代批次沿用 [GpuExchangeProtocol.md](GpuExchangeProtocol.md) 第 9 节的四卡例外。

每个请求有 4 个 rank。`logical_nodes/` 下的测试在 `triton-dist-logical-nodes` 下运行，`logical_nodes` 为 2：`WORLD_SIZE=4`、`LOCAL_WORLD_SIZE=2`，两个节点、各两个 rank，rank = 2 × 节点 + 本地 rank。它在 `one_node/` 下的对照在 `triton-dist` 下运行相同的 harness、输入和输出：一个节点、四个 rank。harness 和 judge 就是 2 个 rank 的请求所用的。judge 对任意 rank 数计算参考值；`test_internode_logical.py` 为四个 rank 植入错误结果，并检查每一个都被标出。

**可见顺序。** launcher 把操作员的 `CUDA_VISIBLE_DEVICES` 中第 2n 和第 2n + 1 项交给逻辑节点 n（`scripts/gpurun/dist.py` 中的 `logical_nodes`），在两个 launcher 下 rank r 都运行在第 r 项上。因此操作员先列出一个卡对的两张 GPU，再列出另一个卡对的两张：`0,1,2,3`、`2,3,4,5` 或 `0,1,4,5`。这样每个逻辑节点持有一个 NVLink 卡对：逻辑节点内部的流量走 NVLink，逻辑节点之间的流量从一个卡对跨到另一个卡对，与集群中节点内和节点间的情形相同。像 `0,2,1,3` 这样的顺序则会把 NVLink 放到逻辑节点之间。`gpurun` 不知道哪些 GPU 组成卡对，所以顺序由操作员决定；它不拒绝四张 GPU 所需的任何东西，而可见 GPU 少于四张时，该批次及其每个测试都返回 `skipped_env`（`scripts/gpurun/test_dist.py`，以及针对这两个批次的 `test_internode_logical.py`）。

**Tutorial 03，`internode-logical-ag03-2x2-001`。** 与 2 个 rank 的请求相同的四个测试，同样的 64 字节；rank r 拥有第 16r 至 16r + 15 字节。在固定版本中读到：2D kernel 启动时每个 rank 对应一个 program（`T03:182`），并把 rank 拆成节点和本地 rank（`T03:125-131`）。两个节点、各两个 rank 时，rank r 的四个 program 是：

| rank r 的 program | 行 | 做什么 |
| --- | --- | --- |
| r | `T03:148-155` | 等待其余三个分段的信号字，每个其他 rank 一个线程。 |
| r xor 2：本地 rank 相同，另一节点 | `T03:135-147` | 把分段 r 以带信号、非阻塞的跨节点 put 发给 rank r xor 2。 |
| r xor 1：另一本地 rank，同一节点 | `T03:156-159`、`T03:169-177` | 把分段 r 以带信号的 put 发给 rank r xor 1。之前没有等待，因为 `peer_node_id == node_id`。 |
| 3 − r：另一本地 rank，另一节点 | `T03:156-177` | **先接收，再转发。** 线程 0 等待信号字 r xor 2，它由 rank r xor 2 在其分段到达 rank r 时设置（`T03:160-166`）；所有线程汇合（`T03:167`）；随后该 program 把分段 r xor 2 以带信号的 put 发给 rank r xor 1（`T03:169-177`）。 |

因此“先接收再转发”的那些行在全部四个 rank 中运行，每个 rank 一个 program。rank r 从本节点的另一个 rank 直接得到分段 r xor 1，从另一节点得到分段 r xor 2，并得到由 rank r xor 1 转发的分段 3 − r，后者是 rank r xor 1 从 rank 3 − r 收到的。在 `one_node` 下（`NNODES=1`），除 r 之外的每个 program 都走 `T03:156-159` 和 `T03:169-177`，且 `peer_node_id == node_id`：三次直接 put，没有跨节点 put，put 之前也没有等待。在到达之前就被转发的分段，在接收方 rank 中是 sentinel，尽管它的信号已被设置；judge 会指出哪些分段不同。

与每逻辑节点一个 rank 的运行相比，除分支之外的变化：

- 信号字。kernel 访问第 0 至 3 个字（`T03:143`、`T03:151`、`T03:163`、`T03:173`）。harness 为每个信号张量分配四个字；教程的程序只分配一个（`T03:276-278`），所以四个 rank 时它会使用张量之后的三个字。
- 规模。每次启动四个 program；每次 put 16 字节。
- Barrier。harness 的两次 barrier 是 NVSHMEM 自身在全部四个 rank 上的 barrier（`UT:304-306`）。
- 链路。在 `logical_nodes` 下，节点内的 put 留在一个 NVLink 卡对上，每个 rank 的跨节点 put 去往另一卡对。在 `one_node` 下，每个 rank 直接向三个 rank 做 put，其中两个在另一卡对上。

本请求没有到达、也不需要的：`supports_p2p_native_atomic()` 和 `has_fullmesh_nvlink()`。Tutorial 03 两者都不导入（`T03:44-47`）。

**Tutorial 06，`internode-logical-rs06-2x2-001`。** 两个测试，`one_node/harness_context` 和 `logical_nodes/harness_context`：只使用 harness 构建的上下文，因为教程自己的构造函数在节点 0 之外会失败（上文已观察到；对该失败的测试不再重复）。输入：每个 rank 一个 1024 × 128 的矩阵，元素为 −64 到 64 之间的整数，转换为 bfloat16。rank r 的预期：四个矩阵之和的第 256r 至 256r + 255 行。四个输入中任意几个之和的绝对值至多为 256，bfloat16 可以精确表示，因此无论加法顺序如何，比较都没有容差。行数为 1024 时，每个归约 tile 仍然落在其张量之内（每个 rank 256 行）。

在固定版本中针对 `world_size` 为 4、`local_world_size` 为 2 读到（`nnodes` 为 2，`M_per_rank` 为 256，`M_per_node` 为 512）：

| 文本 | `one_node`（一个节点、四个 rank） | `logical_nodes`（两个节点、各两个 rank） |
| --- | --- | --- |
| 缓冲区（`T06:188-201`，在 harness 中构建） | scatter 1024 行；每节点缓冲区和 P2P 缓冲区 256 行；8 个信号字；每个列表有四个张量，其中三个是对端的张量。 | scatter 1024 行；每节点缓冲区和 P2P 缓冲区 512 行；8 个信号字；每个列表有两个张量，即该 rank 自己的和本节点另一个 rank 的。 |
| 对节点的循环（`T06:314`、`T06:326`） | 一趟。 | 两趟：先是属于另一节点的行，再是属于本节点的行。 |
| `intra_node_scatter`（`T06:276-294`） | 主机侧把 256 行分别复制到其余三个 rank 的 scatter 缓冲区以及该 rank 自己的缓冲区。 | 每一趟中，主机侧把 256 行**复制到本节点另一个 rank 的 scatter 缓冲区**（`T06:279`、`T06:288-294`，第一次迭代），并把 256 行复制到该 rank 自己的缓冲区：这就是本请求要到达的分支。四个 rank 都走这个分支，各两次。 |
| `barrier_all_on_stream`（`T06:344`） | 一次，在四个 rank 的节点 team 上。 | 两次，在同一个四个 rank 的节点 team 上，而不是在两个 rank 的节点上（见下）。 |
| 每节点的 `ring_reduce`（`T06:349-354`） | 四个 256 行的块求和。 | 每一趟对两个 256 行的块求和：该 rank 在这一趟中的行，按本节点所持有的。 |
| 在 `nnodes > 1` 之下（`T06:357-374`） | 未到达。 | 第一趟：`kernel_inter_node_p2p_for_same_local_rank` 把节点部分和的 256 行 put 给 rank r xor 2（`T06:253-261`）。第二趟：把节点为该 rank 自己算出的部分和复制到它的 P2P 缓冲区（`T06:358-363`）。 |
| 对节点的 `ring_reduce`（`T06:406`） | 复制一个块。 | 两个块求和：本节点的部分和，以及从另一节点收到的部分和。 |

因此 `logical_nodes/harness_context` 的结果取决于向另一本地 rank 的 scatter（每个部分和都包含另一个 rank scatter 过来的行）、跨节点 put 以及两次归约。

**在这台主机的四张 GPU 上，tutorial 06 的 barrier 超出了它自身文本允许的范围。** 两个 launcher 下都是如此，任何可见顺序都无法避免：

- 上下文持有 `BarrierAllContext(True)`（`T06:223`），其 rank 数是 NVSHMEM 节点 team 的大小（`CO:238-241`）。四个 rank 的主机名哈希相同，所以无论是一个节点还是两个逻辑节点，team 都有四个 rank（`init_team_node`，`v3.6.5-0` 的 `src/host/team/team_internal.cpp:1106-1130`；两个 rank 的情形已在 #435 中观察到）。
- 当 `supports_p2p_native_atomic()` 成立时，`barrier_all_on_stream` 启动 compare-and-swap kernel（`CO:257-258`）。该函数只就可见设备 0 和 1 询问驱动（`UT:544-547`）。在 `one_node` 下，设备 0 和 1 是第一个卡对。在 `logical_nodes` 下，一个 rank 看到的是自己卡对的两张 GPU。因此在“卡对、卡对”的可见顺序下，预期每个 rank 得到的回答都是 1（卡对 4–5 在 #435 中回答为 1），每个 rank 都启动 compare-and-swap kernel。
- 在该 kernel 中，每个 rank 对 team 中每个 rank 内存里的一个字执行 `atomic_cas`（`CO:158-163`）：一个 rank 在自己的 NVLink 卡对上，两个在另一卡对上，通过 PCIe 到达。该 kernel 的 docstring 说，经 PCIe 的内存不支持原子操作，不得在那里使用这个 kernel（`CO:155-157`）。
- 换一种顺序，使可见设备 0 和 1 不是一个卡对，则预期回答为 0，`barrier_all_on_stream` 改为启动 `barrier_all_intra_node_non_atomic_block`（`CO:259-262`）。这个 kernel 需要的标志字数是 rank 数的两倍（`CO:185-196`：它的第二轮使用 `symm_flags + num_ranks`），而上下文为每个 rank 只分配一个字（`CO:241`）。所以这条路径会使用其张量之后的字，rank 数是多少都一样。这是阅读过程中读到的第二个缺陷，没有运行过。

两个测试的预测结果：读过的任何材料都无法确定。之所以仍然交付这个请求，是因为每一种结果都有信息量，而且代价有上限（每个测试 300 秒）：

- `ok` 且 `equal`：在 barrier 超出其声明条件运行的同时，scatter、跨节点 put 和归约在这台主机上算出了预期的行。这是关于那些代码行的证据。它不是 barrier 在这种链路上正确的证据。
- `timeout`：barrier 或它之前的某一步没有完成；日志显示每个 rank 打印的最后一行。
- `runtime_error`：日志中有错误信息。

推断，而非保证：如果 GPU 把经 PCIe 的 compare-and-swap 执行为一次读加一次写，barrier 仍然会完成，因为每个标志字在为 0 时只被一个 rank 修改，在为 1 时只被另一个 rank 修改（`CO:161-167`）。GPU 是这样做、拒绝这个操作，还是报错，这里读过的任何材料都没有文档说明。

为了让结果可读，每个 rank 除了打印 barrier 的 team 和 `supports_p2p_native_atomic()` 的回答（作为 `barrier` 返回）之外，还打印驱动对它可见设备中每一对之间原生原子操作的报告。在 `one_node` 下这是四张 GPU 的全部六对。judge 预期两个 launcher 下 `barrier` 都是 r、4、1；第三位为 0 表示前两个可见设备不是一个 NVLink 卡对。

本请求没有到达的：`has_fullmesh_nvlink()`。Tutorial 06 只从库文件导入 `ring_reduce`（`T06:49`），而 `ring_reduce` 询问的是 `has_tma()`（`RS:787-790`）。按其文本（`python/triton_dist/nv_utils.py:199-216`、`298-309`），它在能看到两个卡对的进程中回答假，在只看到一个卡对的进程中回答真，所以 tutorial 08 调用的库函数 `reduce_scatter_multi_node`（`RS:807-810`）在两个 launcher 下会走不同的主机路径。

**不同卡对的 GPU 之间预期使用的传输。** 这是根据 `v3.6.5-0` 的 NVSHMEM 源码做出的预期（读于 2026-11-13；来源及其用途与小节“两张 GPU 之间预期使用的传输”相同），不是观察：

- 当对端在同一主机上，并且 `cudaDeviceCanAccessPeer` 成立（对端可见）或 NVML 报告两个设备之间允许读和写（对端被隐藏）时，P2P 传输授予对对端内存的 load 和 store。只有当 `cudaDeviceGetP2PAttribute` 报告原生原子操作，或 NVML 报告允许原子操作时，它才加上原子操作的能力（`src/host/transport/p2p/p2p.cpp:62-177`）。
- 没有任何传输能到达的对端会使初始化终止（`src/host/topo/topo.cpp:486-491`）。固定版本的启动脚本没有选择远程传输，所以适用 NVSHMEM 的默认值；这台主机上是否会有一个远程传输初始化成功，尚不清楚。
- 当每个对端都有 load 和 store、且至少一个没有原子操作时，作业以“load 和 store”模式运行（`set_job_connectivity`，`src/host/init/init.cu:1651-1730`）。
- 在该模式下，put 向对端被映射的内存复制，set 类型的信号是其后的一次普通 store（`src/include/non_abi/device/common/nvshmemi_common_device.cuh:491-554`）。NVSHMEM 自身的 barrier 用普通 store 发信号，并在本地内存上等待（`src/include/non_abi/device/coll/utils.cuh:41-54`、`coll/barrier.cuh:236-254`）。

推断：如果卡对之间可以通过 PCIe 访问对端，那么 tutorial 03 所做的一切，以及 tutorial 06 的每个 NVSHMEM 操作（其跨节点 kernel 的 put、NVSHMEM 的 barrier）都只需要 load 和 store，预期可以通过与卡对内部相同的映射在卡对之间工作，不经过网卡。唯一需要更多的操作是 tutorial 06 自己的 barrier kernel 中的 compare-and-swap，它不经过 NVSHMEM 的传输选择：它取得被映射的地址（`dl.symm_at`，`CO:161`），自己发出原子操作。

**替代批次（用户于 2026-11-21 决定，#478）。** `internode-logical-rs06-2x2-002` 沿用 harness 构建的上下文，给 barrier 构造函数传入 `is_intra_node=False`。在固定版本中，这会跳过节点组字段和分配（CO:234–243），使 T06:344 通过 CO:254–255 调用 NVSHMEM 全局流 barrier。上文的 load/store 传输模式使用普通 store 发信号。成功时每个 rank 根据上下文返回 `[-1, -1, 2]`（无本地 rank 和组大小，使用全局 barrier）。CAS 对应代码 1，judge 会报告差异。本变体覆盖 T06:279、288–294 的同节点 peer scatter，以及两个逻辑节点的第一轮在 T06:364–374 执行的跨节点 put。它不验证教程的原子 barrier。全局 barrier、peer 复制和 put 能否完成，实际拓扑和链路报告，以及两种 launcher 下两次重复的精确归约行，都要由运行确定。测试使用一台物理主机。

**预期结果。**

| 请求 | 预期 | 否则 |
| --- | --- | --- |
| `internode-logical-ag03-2x2-001` | 每个测试 `ok` 且 `equal`：每个 rank 返回 64 个输入字节。 | 每个测试都是 `runtime_error` 并带有 `Peer GPU … is not accessible`：NVSHMEM 无法跨卡对映射，两个请求都无法用四张 GPU 运行。某一个分段不同：上面的 program 表说明它是经哪条路线送达的。 |
| `internode-logical-rs06-2x2-002` | 两个测试中每个 rank 都应返回精确的归约行和 barrier 报告 `[-1, -1, 2]`。 | barrier 报告不同、缺失输出、超时或 CUDA 错误时须检查。 |

Tutorial 03 已在四个 rank 上通过（#466）。Tutorial 06 的 scatter、barrier 和归约仍待验证。

## 受影响请求与完成门槛

下表记录各请求的当前状态。

| 建议批次 | 计划检查 | 当前处置 |
| --- | --- | --- |
| `internode-ag03-single-host-001` | Tutorial 03 的双本地 rank 1D/2D 路径 | 没有单独的 manifest：`internode-logical-ag03-001` 的 `one_node` 测试就是这项检查。 |
| `internode-rs06-single-host-001` | Tutorial 06 的双本地 rank 路径 | 没有单独的 manifest：`internode-logical-rs06-001` 的 `one_node` 测试就是这项检查。 |
| `internode-a2av-single-host-001` | 显式使用 `local_world_size=2` 的 all-to-all 核心 | 等待 `gpurun` 及开发端适配器／manifest；现有测试假定 8。 |
| `internode-sp-attn-single-host-001` | 双本地 rank 序列并行 attention | 等待 `gpurun` 和 manifest；异节点分支仍未覆盖。 |
| `internode-ag03a-rocm-001` | 原样执行 tutorial 03a | H800 无法提供；需要 AMD 环境或明确审阅的移植。 |
| `internode-logical-env-001` | 两个逻辑节点能否启动；两次 barrier 之间一次 put；不含 kernel | 已运行，每个测试均为 `ok`；结果包未发布。由 `internode-logical-env-002` 取代。 |
| `internode-logical-env-002` | 同一请求，使用新的 ID | 已于 2026-11-12 运行；判定为通过。 |
| `internode-logical-ag03-001` | 在 `triton-dist-logical-nodes` 下运行 tutorial 03，两个逻辑节点、每节点一个 rank：2D all-gather 的跨节点分支；并在 `triton-dist` 下以相同测试作为对照 | 已于 2026-11-12 运行（#434）；2026-11-13 判定为通过。只覆盖逻辑节点。 |
| `internode-logical-rs06-001` | 在同一 launcher 下运行 tutorial 06：`kernel_inter_node_p2p_for_same_local_rank` 以及两个节点上的归约；并在 `triton-dist` 下以相同测试作为对照 | 已于 2026-11-12 运行（#435）；2026-11-13 判定为通过，`logical_nodes/tutorial_context` 按预测失败。只覆盖逻辑节点。 |
| `internode-logical-ag03-2x2-001` | Tutorial 03，两个逻辑节点、每节点两个 rank：节点内转发之前的等待；并以一个节点、四个 rank 上的相同测试作为对照 | 已在 #466 判定通过。 |
| `internode-logical-rs06-2x2-001` | Tutorial 06，两个逻辑节点、每节点两个 rank：向另一本地 rank 的 scatter，再接 P2P kernel；并以一个节点、四个 rank 上的相同测试作为对照 | 公告前已撤回。 |
| `internode-logical-rs06-2x2-002` | 相同的测试与对照，使用全局 NVSHMEM barrier。 | 已准备，等待合并后由协调者公告。 |

协议 v1 下，要求两个物理节点的请求仍应返回 `skipped_env`。不能把逻辑节点运行报告为双物理节点结果；其 `meta.json` 带有标签 `"topology": "logical-nodes"`。

Issue #353 等待 tutorial 06 四 rank 结果的判定。
