/-
S5.1 (#56) draft for sign-off. The checker uses the signed event interface in
EventSpec. A reliance names the release and acquire that a proof needs and
the cell whose visibility it needs. S4.1 supplies the trace conditions,
including the read-from condition that connects such a pair to happens-before.
-/
import VeriTile.Staging.Dist.EventSpec

namespace VeriTile.Dist

/-- UNSIGNED. Owner: S5.2. A release/acquire pair required for the visibility
of a cell. The cell can differ from the synchronization word. -/
structure ScopeReliance where
  cell : Addr
  writer : Agent × Event
  reader : Agent × Event

/-- UNSIGNED. Owner: S5.2. Every required pair must write and read the same
counter and satisfy the signed mode-pairing conditions for the stated reach. -/
def scopeConsistent (reach : ShmemReach) (reliances : List ScopeReliance) : Bool :=
  reliances.all fun r =>
    match r.writer.2.releaseOf?, r.reader.2.acquireOf? with
    | some (c, m), some (c', m') =>
      haveI : Decidable (Mode.Pairs reach r.cell r.writer.1 r.reader.1 m m') := by
        cases m <;> cases m' <;> simp only [Mode.Pairs] <;> infer_instance
      decide (c = c' ∧ Mode.Pairs reach r.cell r.writer.1 r.reader.1 m m')
    | _, _ => false

/-- UNSIGNED. Owner: S5.2. Every requested pair admitted by the checker
satisfies `SyncEdge` for the requested cell. -/
theorem scopeConsistent_sound (reach : ShmemReach) (reliances : List ScopeReliance)
    (h : scopeConsistent reach reliances = true) :
    ∀ r ∈ reliances, SyncEdge reach r.cell r.writer r.reader := by
  sorry

/-- UNSIGNED. Owner: S5.2. A GPU-scope acquire cannot pair with a release
issued from another rank. -/
theorem scopeConsistent_crossRankGpu :
    let flag : Addr := ⟨.global 0, ⟨"flag"⟩, 0⟩
    scopeConsistent .ownRank
      [⟨flag, (.rank 0, .bump ⟨.word flag, .set, 1, .atomic .sys .release⟩),
        (.rank 1, .wait (.word flag) .eq 1 (.atomic .gpu .acquire))⟩] = false := by
  decide

/-- UNSIGNED. Owner: S5.2. Changing the acquire to system scope admits the
same pair in the event interface. -/
theorem scopeConsistent_crossRankSys :
    let flag : Addr := ⟨.global 0, ⟨"flag"⟩, 0⟩
    scopeConsistent .ownRank
      [⟨flag, (.rank 0, .bump ⟨.word flag, .set, 1, .atomic .sys .release⟩),
        (.rank 1, .wait (.word flag) .eq 1 (.atomic .sys .acquire))⟩] = true := by
  decide

/-- UNSIGNED. Owner: S5.3. The two classes of named trust assumptions. -/
inductive TrustAssumptionClass where
  | semanticSource
  | translationCorrectness
  deriving DecidableEq, Repr

/-- UNSIGNED. Owner: S5.3. Metadata attached to a proposition used as an
explicit trust premise. The statement does not carry a proof. -/
structure TrustAssumption where
  name : Lean.Name
  statement : Prop
  sourceOrRationale : String
  affectedKernels : List String
  assumptionClass : TrustAssumptionClass

namespace TrustAssumptionExamples

/-- Example metadata for the semantic entries of PrimitiveSources.md §7.
Each example takes its proposition as an argument until the entry is formalized. -/
private def semanticExample (name : Lean.Name) (statement : Prop) (source : String)
    (affected : List String) : TrustAssumption where
  name := name
  statement := statement
  sourceOrRationale := source
  affectedKernels := affected
  assumptionClass := .semanticSource

example (statement : Prop) : TrustAssumption :=
  semanticExample `undocumented_scope_order_vocabulary statement
    "PrimitiveSources.md §7 A1, undocumented scope and memory order vocabulary"
    ["TD reduce_scatter.py", "TD allgather_gemm.py", "TD common_ops.py",
      "TD gemm_reduce_scatter.py", "TD tutorial 08",
      "TileScale example_allgather_gemm_overlapped.py",
      "TileScale example_allgather_gemm_specialized.py",
      "TileScale example_gemm_ar_specialized.py",
      "TileScale example_gemm_rs_overlapped.py",
      "K-M D2", "K-M D3", "K-M D4", "K-M D5", "K-M D6"]

example (statement : Prop) : TrustAssumption :=
  semanticExample `notify_atomic_release statement
    "PrimitiveSources.md §7 A2, notify release ordering"
    ["Triton-distributed tutorial 01", "Triton-distributed tutorial 08",
      "Triton-distributed gemm_reduce_scatter.py"]

example (statement : Prop) : TrustAssumption :=
  semanticExample `spin_wait_one_blocking_event statement
    "PrimitiveSources.md §7 A3, empty-body spin loops"
    ["K11", "K15", "K16"]

example (statement : Prop) : TrustAssumption :=
  semanticExample `sync_threads_group_barrier statement
    "PrimitiveSources.md §7 A4, the two-argument TileScale group barrier"
    ["K25", "K26", "K28"]

example (statement : Prop) : TrustAssumption :=
  semanticExample `tilescale_barrier_orders_memory statement
    "PrimitiveSources.md §7 A5, memory ordering for TileScale barriers"
    ["K23", "K25", "K26", "K28"]

example (statement : Prop) : TrustAssumption :=
  semanticExample `deepep_v1_wait_scope_order statement
    "PrimitiveSources.md §7 A6, DeepEP v1 default wait scope and order"
    ["K25", "K26", "K28"]

example (statement : Prop) : TrustAssumption :=
  semanticExample `deepep_v1_volatile_load_relaxed statement
    "PrimitiveSources.md §7 A7, DeepEP v1 volatile loads"
    ["K25", "K26"]

example (statement : Prop) : TrustAssumption :=
  semanticExample `p2p_native_atomic_supported statement
    "PrimitiveSources.md §7 A8, the platform's P2P native atomic attribute"
    ["K1", "K11", "K15", "K16", "K25", "K26", "K28"]

example (statement : Prop) : TrustAssumption :=
  semanticExample `grid_barrier_cooperative_sync statement
    "PrimitiveSources.md §7 A9, cooperative-grid rendezvous and memory ordering"
    ["D2 all_to_all_v_2d_kernel", "D2 all_to_all_v_2d_kernel_v2",
      "D3 all_to_all_v_2d_inter_node_kernel", "D4 reduce_topk_reduce_scatter_a2a_intra_node_kernel",
      "D5 reduce_topk_reduce_ar_intra_node_kernel", "D6 _copy_and_reset_and_barrier_all_kernel"]

example (statement : Prop) : TrustAssumption :=
  semanticExample `deepep_v1_calls_read_by_main_rows statement
    "PrimitiveSources.md §7 A10, the main branch's documented rows for the v1 port"
    ["K23", "K24", "K25", "K26", "K27", "K28"]

end TrustAssumptionExamples
end VeriTile.Dist
