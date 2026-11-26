import Lean

namespace VeriTile.Dist

/- Provisional interface from S5.1 (#56), PR #524 at
24de0412fc3f8e7e1d4f177a14bc4c99bbf6792b. -/

/-- The two classes of named trust assumptions. -/
inductive TrustAssumptionClass where
  | semanticSource
  | translationCorrectness
  deriving DecidableEq, Repr

/-- Metadata attached to a proposition used as an explicit trust premise.
The statement does not carry a proof. -/
structure TrustAssumption where
  name : Lean.Name
  statement : Prop
  sourceOrRationale : String
  affectedKernels : List String
  assumptionClass : TrustAssumptionClass

open Lean

namespace Assumption

/- Opaque propositions reserve the names until the source and trace
semantics can state each guarantee in the main target. Proofs that cite
an entry must supply it as a hypothesis. -/

/-- A1. Opaque pending the scoped primitive semantics for undocumented vocabulary. -/
opaque undocumented_scope_order_vocabulary : Prop

/-- A2. Opaque pending the call-to-event interpretation for release updates by notify. -/
opaque notify_atomic_release : Prop

/-- A3. Opaque pending the trace interpretation of empty-body spin loops. -/
opaque spin_wait_one_blocking_event : Prop

/-- A4. Opaque pending the two-argument TileScale group-barrier interpretation. -/
opaque sync_threads_group_barrier : Prop

/-- A5. Opaque pending happens-before for the documented TileScale barrier cases. -/
opaque tilescale_barrier_orders_memory : Prop

/-- A6. Opaque pending translation of the DeepEP v1 wait calls and their modes. -/
opaque deepep_v1_wait_scope_order : Prop

/-- A7. Opaque pending the interpretation of the selected DeepEP v1 volatile loads. -/
opaque deepep_v1_volatile_load_relaxed : Prop

/-- A8. Opaque pending the trace predicate selecting the accessing and resident devices. -/
opaque p2p_native_atomic_supported : Prop

/-- A9. Opaque pending the trace and happens-before interpretation of the grid barrier. -/
opaque grid_barrier_cooperative_sync : Prop

/-- A10. Opaque pending the call-to-event interpretation of the v1 port. -/
opaque deepep_v1_calls_read_by_main_rows : Prop

/-- S3.1 N5′. Opaque until a front end produces a documented atomic update
with an operand function and return value. -/
opaque documented_atomic_update_lowering : Prop

end Assumption

namespace TrustAssumptions

private def semantic (name : Name) (statement : Prop) (source : String)
    (affected : List String) : TrustAssumption where
  name := name
  statement := statement
  sourceOrRationale := source
  affectedKernels := affected
  assumptionClass := .semanticSource

def undocumented_scope_order_vocabulary : TrustAssumption :=
  semantic `undocumented_scope_order_vocabulary
    Assumption.undocumented_scope_order_vocabulary
    "PrimitiveSources.md §7 A1"
    ["Triton-distributed reduce_scatter.py", "Triton-distributed allgather_gemm.py",
      "Triton-distributed common_ops.py", "Triton-distributed gemm_reduce_scatter.py",
      "Triton-distributed tutorial 08", "TileScale example_allgather_gemm_overlapped.py",
      "TileScale example_allgather_gemm_specialized.py", "TileScale example_gemm_ar_specialized.py",
      "TileScale example_gemm_rs_overlapped.py", "K-M D2", "K-M D3", "K-M D4", "K-M D5", "K-M D6"]

def notify_atomic_release : TrustAssumption :=
  semantic `notify_atomic_release Assumption.notify_atomic_release
    "PrimitiveSources.md §7 A2"
    ["Triton-distributed tutorial 01", "Triton-distributed tutorial 08",
      "Triton-distributed gemm_reduce_scatter.py"]

def spin_wait_one_blocking_event : TrustAssumption :=
  semantic `spin_wait_one_blocking_event Assumption.spin_wait_one_blocking_event
    "PrimitiveSources.md §7 A3"
    ["K11", "K15", "K16"]

def sync_threads_group_barrier : TrustAssumption :=
  semantic `sync_threads_group_barrier Assumption.sync_threads_group_barrier
    "PrimitiveSources.md §7 A4"
    ["K25", "K26", "K28"]

def tilescale_barrier_orders_memory : TrustAssumption :=
  semantic `tilescale_barrier_orders_memory Assumption.tilescale_barrier_orders_memory
    "PrimitiveSources.md §7 A5"
    ["K23", "K25", "K26", "K28"]

def deepep_v1_wait_scope_order : TrustAssumption :=
  semantic `deepep_v1_wait_scope_order Assumption.deepep_v1_wait_scope_order
    "PrimitiveSources.md §7 A6"
    ["K25", "K26", "K28"]

def deepep_v1_volatile_load_relaxed : TrustAssumption :=
  semantic `deepep_v1_volatile_load_relaxed Assumption.deepep_v1_volatile_load_relaxed
    "PrimitiveSources.md §7 A7"
    ["K25", "K26"]

def p2p_native_atomic_supported : TrustAssumption :=
  semantic `p2p_native_atomic_supported Assumption.p2p_native_atomic_supported
    "PrimitiveSources.md §7 A8. cudaDevP2PAttrNativeAtomicSupported is a platform condition, a property of the machine of a run, kept in the semantic-source class."
    ["K1", "K11", "K15", "K16", "K25", "K26", "K28"]

def grid_barrier_cooperative_sync : TrustAssumption :=
  semantic `grid_barrier_cooperative_sync Assumption.grid_barrier_cooperative_sync
    "PrimitiveSources.md §7 A9"
    ["D2 all_to_all_v_2d_kernel", "D2 all_to_all_v_2d_kernel_v2",
      "D3 all_to_all_v_2d_inter_node_kernel", "D4 reduce_topk_reduce_scatter_a2a_intra_node_kernel",
      "D5 reduce_topk_allreduce_kernel", "D6 _copy_and_reset_and_barrier_all_kernel"]

def deepep_v1_calls_read_by_main_rows : TrustAssumption :=
  semantic `deepep_v1_calls_read_by_main_rows Assumption.deepep_v1_calls_read_by_main_rows
    "PrimitiveSources.md §7 A10"
    ["K23", "K24", "K25", "K26", "K27", "K28"]

def documented_atomic_update_lowering : TrustAssumption where
  name := `documented_atomic_update_lowering
  statement := Assumption.documented_atomic_update_lowering
  sourceOrRationale :=
    "The function carried by `AccessValue.update` is trusted only at the boundary that lowers " ++
    "a documented source-level atomic to a distributed emission. A producer identifies its " ++
    "primitive, pinned contract, operand function and return behaviour; a plain load, " ++
    "computation and store never becomes one atomic event. At main `90f8e34ed` no front end " ++
    "produces this payload."
  affectedKernels := []
  assumptionClass := .translationCorrectness

/-- The built-in registry entries, pairing each statement and its metadata. -/
def builtinTrustAssumptionDeclarations : Array (Name × Name) :=
  #[(``Assumption.undocumented_scope_order_vocabulary, ``undocumented_scope_order_vocabulary),
      (``Assumption.notify_atomic_release, ``notify_atomic_release),
      (``Assumption.spin_wait_one_blocking_event, ``spin_wait_one_blocking_event),
      (``Assumption.sync_threads_group_barrier, ``sync_threads_group_barrier),
      (``Assumption.tilescale_barrier_orders_memory, ``tilescale_barrier_orders_memory),
      (``Assumption.deepep_v1_wait_scope_order, ``deepep_v1_wait_scope_order),
      (``Assumption.deepep_v1_volatile_load_relaxed, ``deepep_v1_volatile_load_relaxed),
      (``Assumption.p2p_native_atomic_supported, ``p2p_native_atomic_supported),
      (``Assumption.grid_barrier_cooperative_sync, ``grid_barrier_cooperative_sync),
      (``Assumption.deepep_v1_calls_read_by_main_rows, ``deepep_v1_calls_read_by_main_rows),
      (``Assumption.documented_atomic_update_lowering, ``documented_atomic_update_lowering)]

end TrustAssumptions
end VeriTile.Dist
