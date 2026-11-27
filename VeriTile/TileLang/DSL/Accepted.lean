import VeriTile.TileLang.DSL.Ast
import VeriTile.TileLang.DSL.Exports
import VeriTile.TileLang.DSL.Transfer

/-! Executable admission of a manually constructed or quoted source Program. It checks
the source subset only; type/shape specialization and target-specific contracts
are separate from admission.

The A3.1 signature (#83) covers the shapes of the typed source types in `Ast.lean` and
the exclusion list: `syntacticCall_tileLang_excluded` and `syntacticCall_tileLang_closed`
state which `T.` names the TileLang classifier rejects. That a quotation naming one of
them fails to parse is established by the parser tests in tests/lean/TileLangSyntax.lean,
which run every listed name through the real parser; it is not a signed theorem.
`Program.accepted` is not signed. -/
namespace VeriTile.TileLang
open Lean

def sourceIdentifier : Name → Bool
  | .str .anonymous s => (s.toList.head?.any fun c => c.isAlpha || c == '_') &&
      s.toList.all (fun c => c.isAlphanum || c == '_') &&
      !["if","else","return","import","from","def","for","with","as","True","False","None",
        "lambda","while","yield","pass","class","break","continue","assert","and","or","not",
        "in","T","math","tilelang","global","nonlocal","elif","try","except","finally",
        "async","await","del","is","raise"].contains s
  | _ => false

/-- A name of an explicit WGMMA, TCGen05 or proxy-fence instruction: one of six opcode
prefixes, or one of six exports named below. At tile-ai/tilelang@35850c06:
- `tilelang/language/builtin.py` L540 `warpgroup_arrive`, L549 `warpgroup_commit_batch`,
  L558 `warpgroup_wait` and L872 `wait_wgmma` call the device functions of
  `src/tl_templates/cuda/intrin.h` L70–99, which call CUTLASS `cute::warpgroup_arrive`,
  `warpgroup_commit_batch` and `warpgroup_wait` (`wgmma.fence`, `wgmma.commit_group`,
  `wgmma.wait_group`);
- `tilelang/language/allocate.py` L253 `alloc_tmem` and `builtin.py` L277 `deallocate_tmem`
  are lowered by `src/cuda/transform/lower_shared_tmem.cc` to the device functions of
  `src/tl_templates/cuda/tcgen_05.h` L15–58, `tcgen05.alloc` and `tcgen05.dealloc`.
The method and the names kept are in documents/TileLangSubset.md (Explicit exclusions). -/
def explicitInstruction (field : String) : Bool :=
  ["wgmma", "tcgen05", "ptx_wgmma", "ptx_tcgen05", "fence_proxy", "ptx_fence_proxy"].any
    (fun opcode => field == opcode || field.startsWith (opcode ++ "_")) ||
  ["wait_wgmma", "warpgroup_arrive", "warpgroup_commit_batch", "warpgroup_wait",
   "alloc_tmem", "deallocate_tmem"].contains field

def syntacticCall (mode : Mode) (name : Name) : Bool :=
  match name with
  | .str `T field =>
    let low := explicitInstruction field
    (mode != .tileLang || !low) && (exportedNames.contains field ||
      (mode == .tileScale && (low || ["copy", "atomic_add", "tma_copy", "alloc_shared"].contains field)))
  | _ => name == `math.ceil || sourceIdentifier name

/-- Signed (#83, A3.1). The exclusion list: the pinned exports that the TileLang
classifier rejects as calls and values, exactly these 27, the exports that satisfy
`explicitInstruction`. The parser applies `syntacticCall` in `validateUnit`; the parse
failures are tested, not proved (tests/lean/TileLangSyntax.lean). -/
theorem syntacticCall_tileLang_excluded :
    exportedNames.filter (fun field => !syntacticCall .tileLang (.str `T field)) =
      ["alloc_tmem", "deallocate_tmem", "fence_proxy_async", "ptx_tcgen05_mma_blockscaled_ss", "ptx_tcgen05_mma_ss",
       "ptx_tcgen05_mma_ts", "ptx_wgmma_rs", "ptx_wgmma_sp_rs", "ptx_wgmma_sp_ss", "ptx_wgmma_ss",
       "tcgen05_after_thread_sync", "tcgen05_before_thread_sync", "tcgen05_cp_warpx4",
       "tcgen05_gemm", "tcgen05_gemm_blockscaled", "tcgen05_gemm_sp", "tcgen05_mma",
       "tcgen05_mma_arrive", "tcgen05_mma_blockscaled", "tcgen05_sf_warp_transpose",
       "wait_wgmma", "warpgroup_arrive", "warpgroup_commit_batch", "warpgroup_wait",
       "wgmma_gemm", "wgmma_gemm_sp", "wgmma_mma"] := by
  decide +kernel

/-- Signed (#83, A3.1). In TileLang mode the classifier accepts as a call name only a
pinned export outside `explicitInstruction`, `math.ceil` or an unqualified source
identifier. It rejects every other qualified name. -/
theorem syntacticCall_tileLang_closed (n : Name) (h : syntacticCall .tileLang n = true) :
    (∃ field, n = .str `T field ∧ exportedNames.contains field = true ∧
      explicitInstruction field = false) ∨
    n = `math.ceil ∨ sourceIdentifier n = true := by
  unfold syntacticCall at h
  split at h
  · rename_i field
    refine .inl ⟨field, rfl, ?_⟩
    revert h
    cases explicitInstruction field <;>
      simp [show (Mode.tileLang == Mode.tileScale) = false from rfl,
        show (Mode.tileLang != Mode.tileLang) = false from rfl]
  · exact .inr (by simpa using h)

def sourceValueName (n : Name) : Bool := sourceIdentifier n || match n with
  | .str base field => (sourceIdentifier base && ["shape", "dtype"].contains field) ||
      (base == `T && ["float16", "float32", "bfloat16", "int32", "int64", "bool"].contains field) ||
      n == `T.GemmWarpPolicy.FullRow
  | _ => false

private def coordinate (bound : List Name) : Value → Bool
  | .ident n => bound.contains n
  | .integer _ => true
  | .binary op x y => [.add, .sub, .mul, .floorDiv, .mod].contains op &&
      coordinate bound x && coordinate bound y
  | .list xs | .tuple xs => xs.attach.all fun ⟨x, _⟩ => coordinate bound x
  | _ => false
termination_by v => sizeOf v
decreasing_by all_goals decreasing_tactic

/-- A syntactic layout helper can only return a layout of its input's shape,
whose index mapping is built from numeric literals and the bound coordinates. -/
def LayoutHelper.valid (h : LayoutHelper) : Bool :=
  sourceIdentifier h.name && h.name != `range && sourceIdentifier h.param &&
  (match h.shape with | .ident n => n == .str h.param "shape" | _ => false) &&
  !h.coordinates.isEmpty && h.coordinates.all sourceIdentifier && h.coordinates.Nodup &&
  coordinate h.coordinates h.mapping

private def fits (args : List Argument) (count : Nat) (keys : List Name := []) : Bool := Id.run do
  let pos := args.takeWhile fun | .pos _ => true | _ => false
  let rest := args.drop pos.length
  let actual := rest.filterMap fun | .keyword k _ => some k | _ => none
  return pos.length == count && actual.length == rest.length && actual.length == keys.length &&
    keys.all actual.contains

private inductive Context where | expression | statement | iterator | prelude
  deriving BEq, Inhabited

private structure LocalCall where
  name : Name
  arity : Nat
  asValue : Bool
  asStatement : Bool

private abbrev Helpers := List LocalCall

private def callAllowed (mode : Mode) (ctx : Context) (helpers : Helpers) (n : Name) (args : List Argument) : Bool :=
  if ctx == .iterator then match n with
    | `T.Parallel => fits args 1 || fits args 2
    | `T.Pipelined => fits args 1 [`num_stages] || fits args 2 [`num_stages]
    | `range => fits args 1
    | _ => false
  else if ctx == .statement then match n with
    | `T.clear | `T.use_swizzle | `T.annotate_layout => fits args 1
    | `T.copy | `T.fill | `T.atomic_add => fits args 2 ||
        (mode == .tileScale && n == `T.atomic_add && fits args 2 [`dst_pe])
    | `T.tma_copy => fits args 2 [`barrier] ||
        (mode == .tileScale && fits args 2 [`barrier, `leader_thread_extent])
    | `T.mbarrier_arrive => fits args 0 [`mbarrier]
    | `T.mbarrier_wait_parity => fits args 0 [`mbarrier, `parity]
    | `T.reduce_sum => fits args 3 || fits args 2 [`dim]
    | `T.reduce_max => fits args 2 [`dim, `clear]
    | `T.gemm => [[], [`policy], [`transpose_A], [`transpose_B], [`transpose_B, `policy]].any (fun keys => fits args 3 keys)
    | _ => helpers.any fun h => h.asStatement && h.name == n && fits args h.arity
  else if ctx == .prelude then match n with
    | `T.ceildiv | `T.min | `T.max | `T.empty => fits args 2
    | `math.ceil | `T.const => fits args 1
    | _ => false
  else match n with
    | `T.alloc_fragment | `T.alloc_shared => fits args 2 || fits args 1 [`dtype] ||
        (n == `T.alloc_shared && mode == .tileScale && fits args 2 [`scope])
    | `T.ceildiv | `T.max | `T.min | `T.empty | `T.floordiv => fits args 2
    | `T.exp2 | `T.const | `T.infinity | `T.alloc_barrier | `T.log2 | `math.ceil => fits args 1
    | `T.if_then_else => fits args 3
    | _ => helpers.any fun h => h.asValue && n == h.name && fits args h.arity

/-- Unsigned decimal literal: an integer part followed by a fraction, an exponent,
or both. Signs on the entire expression are represented by a separate AST node. -/
private def decimalSpelling (s : String) : Bool := Id.run do
  let chars := s.toList
  let rest ← match chars with
    | '0' :: rest => pure rest
    | c :: rest => if c.isDigit then pure (rest.dropWhile Char.isDigit) else return false
    | [] => return false
  let (fraction, rest) ← match rest with
    | '.' :: c :: rest => if c.isDigit then pure (true, rest.dropWhile Char.isDigit) else return false
    | rest => pure (false, rest)
  match rest with
  | [] => return fraction
  | 'e' :: digits | 'E' :: digits =>
    let digits := match digits with | '+' :: ns | '-' :: ns => ns | ns => ns
    return !digits.isEmpty && digits.all Char.isDigit
  | _ => return false

mutual
private def valueOK (m : Mode) (ctx : Context) (hs : Helpers) : Value → Bool
  | .ident n => sourceValueName n
  | .integer _ | .boolean _ | .string _ => true
  | .decimal s => decimalSpelling s
  | .list xs | .tuple xs => xs.attach.all fun ⟨x, _⟩ => valueOK m ctx hs x
  | .neg x => valueOK m ctx hs x
  | .not x => m == .tileScale && valueOK m ctx hs x
  | .binary op x y => (m == .tileScale || ![Binary.and, .or].contains op) &&
      valueOK m ctx hs x && valueOK m ctx hs y
  | .index n xs => sourceIdentifier n && !xs.isEmpty && xs.attach.all fun ⟨x, _⟩ => indexOK m ctx hs x
  | .conditional a b c => valueOK m ctx hs a && valueOK m ctx hs b && valueOK m ctx hs c
  | .call n xs => callAllowed m ctx hs n xs && xs.attach.all fun ⟨x, _⟩ => argOK m ctx hs x
  | .layout s coords e => ctx != .prelude && !coords.isEmpty && coords.Nodup &&
      coords.all sourceIdentifier && valueOK m ctx hs s && valueOK m ctx hs e
  | .layoutMap n v => ctx != .prelude && sourceIdentifier n && valueOK m ctx hs v
termination_by v => sizeOf v
decreasing_by all_goals decreasing_tactic
private def argOK (m : Mode) (ctx : Context) (hs : Helpers) : Argument → Bool
  | .pos x | .keyword _ x => valueOK m ctx hs x
termination_by a => sizeOf a
decreasing_by all_goals decreasing_tactic
private def indexOK (m : Mode) (ctx : Context) (hs : Helpers) : Index → Bool
  | .atIndex x => valueOK m ctx hs x
  | .slice (some a) (some b) => valueOK m ctx hs a && valueOK m ctx hs b
  | .slice (some x) none | .slice none (some x) => valueOK m ctx hs x
  | .slice none none => true
termination_by i => sizeOf i
decreasing_by all_goals decreasing_tactic
end

private def placeOK (m : Mode) (hs : Helpers) : Place → Bool
  | .variable n => sourceIdentifier n
  | .index n xs => sourceIdentifier n && !xs.isEmpty && xs.all (indexOK m .expression hs)
  | .unpack ns => ns.length ≥ 2 && ns.all sourceIdentifier

private def staticOK (m : Mode) : Statement → Bool
  | .assign (.variable n) x => sourceIdentifier n && valueOK m .prelude [] x
  | .assign (.unpack ns) x => ns.length ≥ 2 && ns.all sourceIdentifier && valueOK m .prelude [] x
  | .annotate n s d => sourceIdentifier n && valueOK m .prelude [] s && valueOK m .prelude [] d
  | .branch cond a b => valueOK m .prelude [] cond &&
      a.attach.all (fun ⟨x, _⟩ => staticOK m x) && b.attach.all (fun ⟨x, _⟩ => staticOK m x)
  | .assertStatic cond _ => valueOK m .prelude [] cond
  | _ => false
termination_by s => sizeOf s
decreasing_by all_goals decreasing_tactic

private def statementOK (m : Mode) (hs : Helpers) (insideKernel : Bool) : Statement → Bool
  | .assign p x => placeOK m hs p && valueOK m .expression hs x
  | .update p op x => [.add, .sub, .div, .mul].contains op && placeOK m hs p &&
      (match p with | .unpack _ => false | _ => true) && valueOK m .expression hs x
  | .invoke n args => callAllowed m .statement hs n args && args.all (argOK m .expression hs)
  | .ret x => !insideKernel && valueOK m .expression hs x
  | .annotate n s d => sourceIdentifier n && valueOK m .expression hs s && valueOK m .expression hs d
  | .branch c a b => valueOK m .expression hs c &&
      a.attach.all (fun ⟨x, _⟩ => statementOK m hs insideKernel x) &&
      b.attach.all (fun ⟨x, _⟩ => statementOK m hs insideKernel x)
  | .loop bs iter args body => !body.isEmpty && bs.all sourceIdentifier && bs.Nodup &&
      callAllowed m .iterator [] iter args && bs.length == (if iter == `T.Parallel then args.length else 1) &&
      args.all (argOK m .expression hs) && body.attach.all fun ⟨x, _⟩ => statementOK m hs insideKernel x
  | .kernel .. => false
  | .role n body => !body.isEmpty && valueOK m .expression hs n &&
      body.attach.all fun ⟨x, _⟩ => statementOK m hs insideKernel x
  | .whileLoop c body => m == .tileScale && valueOK m .expression hs c &&
      !body.isEmpty && body.attach.all fun ⟨x, _⟩ => statementOK m hs insideKernel x
  | .breakLoop | .continueLoop => m == .tileScale
  | .assertStatic .. => false
termination_by s => sizeOf s
decreasing_by all_goals decreasing_tactic

private def ParamName : Parameter → Name
  | .required n | .optional n _ | .tensor n .. => n

private def parametersOK (m : Mode) (ps : List Parameter) : Bool :=
  (ps.map ParamName).Nodup && ps.all (fun p => sourceIdentifier (ParamName p)) &&
  (ps.dropWhile (fun | .optional .. => false | _ => true)).all (fun | .optional .. => true | _ => false) &&
  ps.all fun
    | .required _ => true
    | .optional _ x => valueOK m .prelude [] x
    | .tensor _ s d => valueOK m .prelude [] s && valueOK m .prelude [] d

private def optionsOK (opts : List JitOption) : Bool :=
  (opts.map fun | .outputs _ => true | .flag .. => false).Nodup &&
  opts.all fun
    | .outputs xs => !xs.isEmpty
    | .flag (.literal key) _ => key == "tl.disable_warp_specialized"
    | .flag (.symbol key) _ => [`tilelang.PassConfigKey.TL_ENABLE_FAST_MATH,
        `tilelang.PassConfigKey.TL_DISABLE_WARP_SPECIALIZED].contains key

private def launchOK (m : Mode) (hs : Helpers) : Statement → Bool
  | .kernel args bs body => !body.isEmpty && bs.length ≥ 1 && bs.length ≤ 3 &&
      bs.Nodup && bs.all sourceIdentifier && (fits args bs.length || fits args bs.length [`threads]) &&
      args.all (argOK m .expression hs) && body.all (statementOK m hs true)
  | _ => false

private def directOK (m : Mode) (hs : Helpers) (p : Procedure) : Bool := Id.run do
  let prelude := p.body.takeWhile (staticOK m)
  let [.kernel args bs body, .ret out] := p.body.drop prelude.length | return false
  return launchOK m hs (.kernel args bs body) && valueOK m .expression hs out

/-- Admission checks a complete typed source object, including hand-built ones, for the
selected mode, option, outer shape, helper scope/arity, call signatures and all nested
operands. It does not assert that every admitted construct has executable semantics. -/
def Program.accepted (p : Program) : Bool := Id.run do
  unless p.tmaSourcesAccepted && (p.layouts.map (·.name)).Nodup && p.layouts.all LayoutHelper.valid &&
      optionsOK (p.jit.getD []) do return false
  let mut hs : Helpers := p.layouts.map fun h => ⟨h.name, 1, true, false⟩
  match p.definition with
  | .direct f =>
    return p.jit.isSome && sourceIdentifier f.name && !(hs.any (·.name == f.name)) &&
      parametersOK p.mode f.params && directOK p.mode hs f
  | .factory f macros primFunc ret =>
    unless f.name != primFunc.name && sourceIdentifier f.name && sourceIdentifier primFunc.name &&
        ret == primFunc.name && parametersOK p.mode f.params && f.body.all (staticOK p.mode) &&
        parametersOK p.mode primFunc.params && primFunc.params.all (fun | .tensor .. => true | _ => false) &&
        !hs.any (fun h => h.name == f.name || h.name == primFunc.name) do return false
    for mac in macros do
      unless sourceIdentifier mac.name && mac.name != `range && mac.name != f.name && mac.name != primFunc.name && !hs.any (·.name == mac.name) &&
          parametersOK p.mode mac.params && mac.params.all (fun | .required _ => true | _ => false) &&
          !mac.body.isEmpty && mac.body.all (statementOK p.mode hs false) do return false
      let returns := mac.body.getLast?.any fun | .ret _ => true | _ => false
      hs := ⟨mac.name, mac.params.length, returns, true⟩ :: hs
    let [launch] := primFunc.body.dropWhile (staticOK p.mode) | return false
    return launchOK p.mode hs launch

end VeriTile.TileLang
