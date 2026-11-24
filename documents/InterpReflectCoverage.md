# Reflection coverage of the example kernels

The reflector produced a computable mirror and a kernel-checked `toReal_mirror` equation for **62 of the 68** kernel definitions in the 18 `bench/examples/*/Kernels.lean` files. Each real parameter in an original definition is instantiated at the cast of the corresponding rational parameter of its mirror. The equations hold for every such instantiation.

Four definitions project a component kernel body during construction. Two others dispatch on symbolic dimensions. Their six rejection tests pin the present limits of reflection. The rows count kernel definitions, including distinct wrappers. Three parameterized mirrors also have execution tests: Adam update and the scalar depth and width hyper-connections.

The following table is the output of `lake env lean tests/lean/InterpReflectBench.lean` after `lake build tests.lean.InterpReflectBench`. Its final `#eval` inspects the declarations returning `ComputeKernel` in each imported example module and looks up the corresponding generated theorem. The source links identify the definitions at the tested revision.

| Example source | Kernel | Elaboration result |
| --- | --- | --- |
| [AdamUpdateGridLaunch](../bench/examples/AdamUpdateGridLaunch/Kernels.lean#L107) | `originalKernel` | Reflected |
| [AdamUpdateGridLaunch](../bench/examples/AdamUpdateGridLaunch/Kernels.lean#L110) | `optimizedKernel` | Reflected |
| [AdamUpdateGridLaunch](../bench/examples/AdamUpdateGridLaunch/Kernels.lean#L19) | `update_fn_kernel` | Reflected |
| [AdamUpdateGridLaunch](../bench/examples/AdamUpdateGridLaunch/Kernels.lean#L63) | `commuted_update_kernel` | Reflected |
| [FlatVectorAdd](../bench/examples/FlatVectorAdd/Kernels.lean#L14) | `addMaskedKernel` | Reflected |
| [FlatVectorAdd](../bench/examples/FlatVectorAdd/Kernels.lean#L25) | `commutedKernel` | Reflected |
| [FlatVectorAdd](../bench/examples/FlatVectorAdd/Kernels.lean#L36) | `originalKernel` | Reflected |
| [FlatVectorAdd](../bench/examples/FlatVectorAdd/Kernels.lean#L39) | `optimizedKernel` | Reflected |
| [FloatDTypeAdd](../bench/examples/FloatDTypeAdd/Kernels.lean#L14) | `floatAddKernel` | Reflected |
| [FloatDTypeAdd](../bench/examples/FloatDTypeAdd/Kernels.lean#L28) | `commutedKernel` | Reflected |
| [FloatDTypeAdd](../bench/examples/FloatDTypeAdd/Kernels.lean#L42) | `originalKernel` | Reflected |
| [FloatDTypeAdd](../bench/examples/FloatDTypeAdd/Kernels.lean#L45) | `optimizedKernel` | Reflected |
| [FloatDTypeSoftmax](../bench/examples/FloatDTypeSoftmax/Kernels.lean#L15) | `floatStableSoftmaxKernel` | Reflected |
| [FloatDTypeSoftmax](../bench/examples/FloatDTypeSoftmax/Kernels.lean#L28) | `floatSoftmaxRecipKernel` | Reflected |
| [FloatDTypeSoftmax](../bench/examples/FloatDTypeSoftmax/Kernels.lean#L43) | `commonPrefix` | Prefix extraction projects the kernel body via `ComputeKernel.rec`. |
| [FloatDTypeSoftmax](../bench/examples/FloatDTypeSoftmax/Kernels.lean#L47) | `originalKernel` | Reflected |
| [FloatDTypeSoftmax](../bench/examples/FloatDTypeSoftmax/Kernels.lean#L50) | `reciprocalKernel` | Reflected |
| [FusedLayerNorm](../bench/examples/FusedLayerNorm/Kernels.lean#L17) | `twoPassLayerNormKernel` | Reflected |
| [FusedLayerNorm](../bench/examples/FusedLayerNorm/Kernels.lean#L36) | `fusedLayerNormKernel` | Reflected |
| [FusedSiLU](../bench/examples/FusedSiLU/Kernels.lean#L14) | `fusedSiLUKernel` | Reflected |
| [FusedSiLU](../bench/examples/FusedSiLU/Kernels.lean#L32) | `siluStepGateKernel` | Reflected |
| [FusedSiLU](../bench/examples/FusedSiLU/Kernels.lean#L47) | `siluStepSiluKernel` | Reflected |
| [FusedSiLU](../bench/examples/FusedSiLU/Kernels.lean#L61) | `siluStepResidualKernel` | Reflected |
| [FusedSiLU](../bench/examples/FusedSiLU/Kernels.lean#L71) | `unfusedSiLUKernel` | Sequential composition projects component bodies via `ComputeKernel.rec`. |
| [FusedSwiglu](../bench/examples/FusedSwiglu/Kernels.lean#L15) | `swiglu_fused_kernel` | Reflected |
| [FusedSwiglu](../bench/examples/FusedSwiglu/Kernels.lean#L32) | `silu_step_kernel` | Reflected |
| [FusedSwiglu](../bench/examples/FusedSwiglu/Kernels.lean#L47) | `mul_step_kernel` | Reflected |
| [FusedSwiglu](../bench/examples/FusedSwiglu/Kernels.lean#L58) | `swiglu_unfused` | Sequential composition projects component bodies via `ComputeKernel.rec`. |
| [HyperConnectionsDepth](../bench/examples/HyperConnectionsDepth/Kernels.lean#L122) | `mhcDepthConnectionKernel` | Matching symbolic dimensions leaves the branch unknown in the `toReal` equation. |
| [HyperConnectionsDepth](../bench/examples/HyperConnectionsDepth/Kernels.lean#L127) | `originalKernel` | Reflected |
| [HyperConnectionsDepth](../bench/examples/HyperConnectionsDepth/Kernels.lean#L129) | `matrixOriginal` | Reflected |
| [HyperConnectionsDepth](../bench/examples/HyperConnectionsDepth/Kernels.lean#L17) | `matrixKernel` | Reflected |
| [HyperConnectionsDepth](../bench/examples/HyperConnectionsDepth/Kernels.lean#L53) | `scalarKernel` | Reflected |
| [HyperConnectionsDepth](../bench/examples/HyperConnectionsDepth/Kernels.lean#L70) | `optimizedKernel` | Reflected |
| [HyperConnectionsDepth](../bench/examples/HyperConnectionsDepth/Kernels.lean#L91) | `matrixOptimizedKernel` | Reflected |
| [HyperConnectionsWidth](../bench/examples/HyperConnectionsWidth/Kernels.lean#L105) | `optimizedKernel` | Reflected |
| [HyperConnectionsWidth](../bench/examples/HyperConnectionsWidth/Kernels.lean#L128) | `matrixMiddleKernel` | Reflected |
| [HyperConnectionsWidth](../bench/examples/HyperConnectionsWidth/Kernels.lean#L17) | `matrixKernel` | Reflected |
| [HyperConnectionsWidth](../bench/examples/HyperConnectionsWidth/Kernels.lean#L175) | `matrixOptimizedKernel` | Reflected |
| [HyperConnectionsWidth](../bench/examples/HyperConnectionsWidth/Kernels.lean#L217) | `mhcWidthConnectionKernel` | Matching symbolic dimensions leaves the branch unknown in the `toReal` equation. |
| [HyperConnectionsWidth](../bench/examples/HyperConnectionsWidth/Kernels.lean#L222) | `originalKernel` | Reflected |
| [HyperConnectionsWidth](../bench/examples/HyperConnectionsWidth/Kernels.lean#L224) | `matrixOriginal` | Reflected |
| [HyperConnectionsWidth](../bench/examples/HyperConnectionsWidth/Kernels.lean#L64) | `scalarKernel` | Reflected |
| [HyperConnectionsWidth](../bench/examples/HyperConnectionsWidth/Kernels.lean#L82) | `middleKernel` | Reflected |
| [LogExp](../bench/examples/LogExp/Kernels.lean#L15) | `originalKernel` | Reflected |
| [LogExp](../bench/examples/LogExp/Kernels.lean#L24) | `optimizedKernel` | Reflected |
| [OnlineSoftmax](../bench/examples/OnlineSoftmax/Kernels.lean#L26) | `stableSoftmaxKernel` | Reflected |
| [OnlineSoftmax](../bench/examples/OnlineSoftmax/Kernels.lean#L39) | `onlineSoftmaxKernel` | Reflected |
| [OnlineSoftmax](../bench/examples/OnlineSoftmax/Kernels.lean#L59) | `batchSoftmaxKernel` | Reflected |
| [RowWiseMax](../bench/examples/RowWiseMax/Kernels.lean#L13) | `rowWiseMaxKernel` | Reflected |
| [RowWiseMax](../bench/examples/RowWiseMax/Kernels.lean#L22) | `inlinedKernel` | Reflected |
| [RowWiseSum](../bench/examples/RowWiseSum/Kernels.lean#L13) | `rowWiseSumKernel` | Reflected |
| [RowWiseSum](../bench/examples/RowWiseSum/Kernels.lean#L22) | `reversedKernel` | Reflected |
| [SoftmaxReciprocal](../bench/examples/SoftmaxReciprocal/Kernels.lean#L15) | `stableSoftmaxKernel` | Reflected |
| [SoftmaxReciprocal](../bench/examples/SoftmaxReciprocal/Kernels.lean#L27) | `softmaxRecipKernel` | Reflected |
| [SoftmaxReciprocal](../bench/examples/SoftmaxReciprocal/Kernels.lean#L41) | `commonPrefix` | Prefix extraction projects the kernel body via `ComputeKernel.rec`. |
| [SoftmaxReciprocal](../bench/examples/SoftmaxReciprocal/Kernels.lean#L45) | `originalKernel` | Reflected |
| [SoftmaxReciprocal](../bench/examples/SoftmaxReciprocal/Kernels.lean#L48) | `reciprocalKernel` | Reflected |
| [SoftmaxStable](../bench/examples/SoftmaxStable/Kernels.lean#L13) | `naiveSoftmaxKernel` | Reflected |
| [SoftmaxStable](../bench/examples/SoftmaxStable/Kernels.lean#L24) | `stableSoftmaxKernel` | Reflected |
| [StableLogSumExp](../bench/examples/StableLogSumExp/Kernels.lean#L13) | `directLSEKernel` | Reflected |
| [StableLogSumExp](../bench/examples/StableLogSumExp/Kernels.lean#L24) | `optimizedLSEKernel` | Reflected |
| [VectorAdd](../bench/examples/VectorAdd/Kernels.lean#L14) | `addKernel` | Reflected |
| [VectorAdd](../bench/examples/VectorAdd/Kernels.lean#L28) | `commutedKernel` | Reflected |
| [VectorAdd](../bench/examples/VectorAdd/Kernels.lean#L42) | `originalKernel` | Reflected |
| [VectorAdd](../bench/examples/VectorAdd/Kernels.lean#L45) | `optimizedKernel` | Reflected |
| [Welford](../bench/examples/Welford/Kernels.lean#L16) | `twopassWelfordKernel` | Reflected |
| [Welford](../bench/examples/Welford/Kernels.lean#L32) | `onlineWelfordKernel` | Reflected |
