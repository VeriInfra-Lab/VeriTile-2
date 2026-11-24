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

/- The signed event interface lives in staging. These opaque propositions
reserve the names and carry the proof author's explicit contract as a parameter.
Elaborating a declaration or its metadata introduces no proof of that contract. -/

/-- A1. Opaque pending the scoped primitive semantics for undocumented vocabulary. -/
opaque undocumented_scope_order_vocabulary (contract : Prop) : Prop := contract

/-- A2. Opaque pending the call-to-event interpretation for release updates by notify. -/
opaque notify_atomic_release (contract : Prop) : Prop := contract

/-- A3. Opaque pending the trace interpretation of empty-body spin loops. -/
opaque spin_wait_one_blocking_event (contract : Prop) : Prop := contract

/-- A4. Opaque pending the two-argument TileScale group-barrier interpretation. -/
opaque sync_threads_group_barrier (contract : Prop) : Prop := contract

/-- A5. Opaque pending happens-before for the documented TileScale barrier cases. -/
opaque tilescale_barrier_orders_memory (contract : Prop) : Prop := contract

/-- A6. Opaque pending translation of the DeepEP v1 wait calls and their modes. -/
opaque deepep_v1_wait_scope_order (contract : Prop) : Prop := contract

/-- A7. Opaque pending the interpretation of the selected DeepEP v1 volatile loads. -/
opaque deepep_v1_volatile_load_relaxed (contract : Prop) : Prop := contract

/-- A8. Opaque pending the trace predicate selecting the accessing and resident devices. -/
opaque p2p_native_atomic_supported (contract : Prop) : Prop := contract

/-- A9. Opaque pending the trace and happens-before interpretation of the grid barrier. -/
opaque grid_barrier_cooperative_sync (contract : Prop) : Prop := contract

/-- A10. Opaque pending the call-to-event interpretation of the v1 port. -/
opaque deepep_v1_calls_read_by_main_rows (contract : Prop) : Prop := contract

end Assumption

namespace TrustAssumptions

private def semantic (name : Name) (statement : Prop) (source : String)
    (affected : List String) : TrustAssumption where
  name := name
  statement := statement
  sourceOrRationale := source
  affectedKernels := affected
  assumptionClass := .semanticSource

def A1 (contract : Prop) : TrustAssumption :=
  semantic `undocumented_scope_order_vocabulary
    (Assumption.undocumented_scope_order_vocabulary contract)
    "PrimitiveSources.md §7 A1 (E-TD1, E-TD8, E-TD14, E-TD16, E-TS5, E-TS13, E-TR1, E-CU1, E-CU3, E-CU4)"
    ["Triton-distributed reduce_scatter.py", "Triton-distributed allgather_gemm.py",
      "Triton-distributed common_ops.py", "Triton-distributed gemm_reduce_scatter.py",
      "Triton-distributed tutorial 08", "TileScale example_allgather_gemm_overlapped.py",
      "TileScale example_allgather_gemm_specialized.py", "TileScale example_gemm_ar_specialized.py",
      "TileScale example_gemm_rs_overlapped.py", "K-M D2", "K-M D3", "K-M D4", "K-M D5", "K-M D6"]

def A2 (contract : Prop) : TrustAssumption :=
  semantic `notify_atomic_release (Assumption.notify_atomic_release contract)
    "PrimitiveSources.md §7 A2 (E-TD2, E-TD3, E-TD10, E-TD11)"
    ["Triton-distributed tutorial 01", "Triton-distributed tutorial 08",
      "Triton-distributed gemm_reduce_scatter.py"]

def A3 (contract : Prop) : TrustAssumption :=
  semantic `spin_wait_one_blocking_event (Assumption.spin_wait_one_blocking_event contract)
    "PrimitiveSources.md §7 A3 (E-TD8, E-CU6, LIT-a03, LIT-a06)"
    ["K11", "K15", "K16"]

def A4 (contract : Prop) : TrustAssumption :=
  semantic `sync_threads_group_barrier (Assumption.sync_threads_group_barrier contract)
    "PrimitiveSources.md §7 A4 (E-TS15, EventControlFlow.md §§1.3 and 8)"
    ["K25", "K26", "K28"]

def A5 (contract : Prop) : TrustAssumption :=
  semantic `tilescale_barrier_orders_memory (Assumption.tilescale_barrier_orders_memory contract)
    "PrimitiveSources.md §7 A5 (E-TS15, E-TS18, E-CU2, E-CU7, E-CU8, LIT-a08)"
    ["K23", "K25", "K26", "K28"]

def A6 (contract : Prop) : TrustAssumption :=
  semantic `deepep_v1_wait_scope_order (Assumption.deepep_v1_wait_scope_order contract)
    "PrimitiveSources.md §7 A6 (E-TS6, E-TS16, DeepEPInventory.md §4.2)"
    ["K25", "K26", "K28"]

def A7 (contract : Prop) : TrustAssumption :=
  semantic `deepep_v1_volatile_load_relaxed (Assumption.deepep_v1_volatile_load_relaxed contract)
    "PrimitiveSources.md §7 A7 (E-TS13, E-TS17, LIT-b12)"
    ["K25", "K26"]

def A8 (contract : Prop) : TrustAssumption :=
  semantic `p2p_native_atomic_supported (Assumption.p2p_native_atomic_supported contract)
    "PrimitiveSources.md §7 A8 (E-CU5, TD-KCO:155–157, I10)"
    ["K1", "K11", "K15", "K16", "K25", "K26", "K28"]

def A9 (contract : Prop) : TrustAssumption :=
  semantic `grid_barrier_cooperative_sync (Assumption.grid_barrier_cooperative_sync contract)
    "PrimitiveSources.md §7 A9 (TD-KCO:62–64 and 110–112, W4, I1)"
    ["D2 all_to_all_v_2d_kernel", "D2 all_to_all_v_2d_kernel_v2",
      "D3 all_to_all_v_2d_inter_node_kernel", "D4 reduce_topk_reduce_scatter_a2a_intra_node_kernel",
      "D5 reduce_topk_allreduce_kernel", "D6 _copy_and_reset_and_barrier_all_kernel"]

def A10 (contract : Prop) : TrustAssumption :=
  semantic `deepep_v1_calls_read_by_main_rows (Assumption.deepep_v1_calls_read_by_main_rows contract)
    "PrimitiveSources.md §7 A10 (§5.5, E-TS3, E-TS5, E-TS6, E-TS8, E-TS16, E-TS19)"
    ["K23", "K24", "K25", "K26", "K27", "K28"]

/-- The built-in registry entries, pairing each statement and its metadata. -/
def builtinTrustAssumptionDeclarations : Array (Name × Name) :=
  #[(``Assumption.undocumented_scope_order_vocabulary, ``A1),
      (``Assumption.notify_atomic_release, ``A2),
      (``Assumption.spin_wait_one_blocking_event, ``A3),
      (``Assumption.sync_threads_group_barrier, ``A4),
      (``Assumption.tilescale_barrier_orders_memory, ``A5),
      (``Assumption.deepep_v1_wait_scope_order, ``A6),
      (``Assumption.deepep_v1_volatile_load_relaxed, ``A7),
      (``Assumption.p2p_native_atomic_supported, ``A8),
      (``Assumption.grid_barrier_cooperative_sync, ``A9),
      (``Assumption.deepep_v1_calls_read_by_main_rows, ``A10)]

end TrustAssumptions
end VeriTile.Dist
