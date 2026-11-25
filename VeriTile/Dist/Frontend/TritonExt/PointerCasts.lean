import VeriTile.Dist.Event
import VeriTile.Triton.Semantics.State
import VeriTile.Triton.DSL.PythonFullConstructors

/-! Kernel-level typed pointer views (#548). The launch binding supplies allocation
provenance, extent, base alignment and the **actual cell dtype** of each
physical buffer. Pointer formation need not dereference the declared pointee.
Changing that access unit between device launches requires that no device read
observe the previous contents. For T04 the byte-exact host gather is an additional
precondition of #156. See `documents/dist/PointerCasts.md` for the source pins.

`with_pointer_views … in triton { … }` checks one active lane's address operations
and produces signed-model cell ranges. It does not execute a load, store or
external transfer. An NVSHMEM signal wait can observe a single supplied memory
snapshot through `SignalWait.observe`. Numeric casts and bitcasts use the ordinary compute frontend.
-/
namespace VeriTile.Dist.Frontend.TritonExt.PointerCasts

open VeriTile.Triton (SourceDType RegionName MemCell)
open Lean Elab Term
open VeriTile.Triton.DSL

private def byteWidth : SourceDType → Except String Nat
  | .i8 | .u8 | .f8e4 | .f8e5 => .ok 1
  | .i16 | .u16 | .fp16 | .bf16 => .ok 2
  | .i32 | .u32 | .fp32 => .ok 4
  | .i64 | .u64 | .fp64 => .ok 8
  | .boolean => .error "pointer view: sub-byte elements are unsupported"

structure Allocation where
  space : Space
  region : RegionName
  baseByte : Nat
  extentBytes : Nat
  unit : SourceDType
  symmetric : Bool := Bool.false
  deriving DecidableEq

structure Argument where
  name : String
  allocation : Allocation
  declared : SourceDType

structure Launch where
  pointers : List Argument := []
  integers : List (String × Int) := []

structure Pointer where
  allocation : Allocation
  /-- Relative coordinate used only for static unit conversion. -/
  byteOffset : Nat
  /-- `none` is an opaque ABI void pointer. -/
  pointee : Option SourceDType

inductive Operand where
  | index (value : Int)
  | pointer (value : Pointer)
  | payload

inductive AddressExpr where
  | var (name : String)
  | literal (value : Nat)
  | add : AddressExpr → AddressExpr → AddressExpr
  | sub : AddressExpr → AddressExpr → AddressExpr
  | mul : AddressExpr → AddressExpr → AddressExpr
  | cast (input : AddressExpr) (target : Option SourceDType)

inductive Instruction where
  | assign (name : String) (value : AddressExpr)
  | load (name : String) (pointer : AddressExpr)
  | store (pointer value : AddressExpr)
  | wait (signal : AddressExpr) (cmp : Cmp) (target : AddressExpr)
  | transfer (put : Bool) (destination source count peer : AddressExpr)

structure CellRange where
  first : Addr
  cells : Nat
  deriving DecidableEq

/-- NV:579 reinterprets the physical integer word at this address for an
unsigned comparison. The allocation supplies the tag used for the actual read. -/
structure SignalWait where
  address : Addr
  signedStorage : Bool
  cmp : Cmp
  target : BitVec 64
  deriving DecidableEq

/-- One observation of the pinned extern: return its uint64 result when ready,
or `none` while blocked. Supply the launch's authoritative cell map
(`DistState.cell`). An unrepresentable mathematical integer is not a word. -/
def SignalWait.observe (w : SignalWait) (cell : Addr → MemCell) :
    Except String (Option (BitVec 64)) := do
  let stored := cell w.address
  let bits ← if w.signedStorage then do
    let some i := stored.readAs .int | throw "signal wait: expected an int64 cell"
    let bits := BitVec.ofInt 64 i
    unless bits.toInt == i do throw "signal wait: stored value outside int64 range"
    pure bits
  else do
    let some n := stored.readAs .nat | throw "signal wait: expected a uint64 cell"
    let bits := BitVec.ofNat 64 n
    unless bits.toNat == n do throw "signal wait: stored value outside uint64 range"
    pure bits
  letI : Decidable (w.cmp.holds bits.toNat w.target.toNat) := by
    cases w.cmp <;> unfold Cmp.holds <;> infer_instance
  return if w.cmp.holds bits.toNat w.target.toNat then some bits else none

inductive Access where
  | wait (signal : SignalWait)
  | read (dtype : SourceDType) (range : CellRange)
  | write (dtype : SourceDType) (range : CellRange)
  | put (destination source : CellRange)
  | get (destination source : CellRange)
  deriving DecidableEq

private def natIndex (n : Int) : Except String Nat :=
  if n < 0 then .error "pointer view: negative address, count or peer" else .ok n.toNat

private def Pointer.checkAlignment (p : Pointer) : Except String Pointer := do
  if let some dtype := p.pointee then
    let w ← byteWidth dtype
    unless p.byteOffset % w == 0 && (p.allocation.baseByte + p.byteOffset) % w == 0 do
      throw "pointer view: offset or base is not aligned to the target element width"
  return p

private def Pointer.advance (p : Pointer) (delta : Int) : Except String Operand := do
  let some dtype := p.pointee | throw "pointer view: arithmetic on void pointers is unsupported"
  let n ← natIndex (Int.ofNat p.byteOffset + delta * Int.ofNat (← byteWidth dtype))
  unless n ≤ p.allocation.extentBytes do throw "pointer view: pointer outside allocation"
  return .pointer { p with byteOffset := n }

private def Pointer.range (p : Pointer) (bytes : Nat) : Except String CellRange := do
  let unit ← byteWidth p.allocation.unit
  unless p.byteOffset % unit == 0 do throw "pointer view: transfer start is not cell aligned"
  unless bytes % unit == 0 do throw "pointer view: byte count is not divisible by the buffer unit"
  unless p.byteOffset + bytes ≤ p.allocation.extentBytes do throw "pointer view: access outside allocation"
  return ⟨⟨p.allocation.space, p.allocation.region, p.byteOffset / unit⟩, bytes / unit⟩

private def Pointer.dereference (p : Pointer) : Except String (SourceDType × CellRange) := do
  let some dtype := p.pointee | throw "pointer view: cannot dereference a void pointer"
  let width ← byteWidth dtype
  unless dtype == p.allocation.unit do
    if width != (← byteWidth p.allocation.unit) then
      throw "pointer view: mixed access widths or incorrect launch unit for this buffer"
    throw "pointer view: access dtype reinterprets the allocation unit"
  return (dtype, ← p.range width)

private def indexValue : Operand → Except String Int
  | .index i => .ok i
  | _ => .error "pointer view: expected an integer"

private def ptrValue : Operand → Except String Pointer
  | .pointer p => .ok p
  | _ => .error "pointer view: expected a pointer"

private def convert (allocations : List Allocation) (input : Operand) (target : Option SourceDType) :
    Except String Operand := do
  let p ← match input with
    | .pointer p => pure { p with pointee := target }
    | .index i => do
      let n ← natIndex i
      match allocations.filter (fun a => a.baseByte ≤ n && n < a.baseByte + a.extentBytes) with
      | [a] => pure ⟨a, n - a.baseByte, target⟩
      | _ => throw "pointer view: integer address needs a unique allocation provenance"
    | .payload => throw "pointer view: integer or pointer cast operand required"
  return .pointer (← p.checkAlignment)

private def eval (allocations : List Allocation) (env : List (String × Operand)) :
    AddressExpr → Except String Operand
  | .var name => env.lookup name |>.elim (.error s!"pointer view: unknown name {name}") .ok
  | .literal n => .ok (.index n)
  | .cast input target => do convert allocations (← eval allocations env input) target
  | .mul x y => do
    return .index ((← indexValue (← eval allocations env x)) * (← indexValue (← eval allocations env y)))
  | .add x y => do
    match ← eval allocations env x, ← eval allocations env y with
    | .pointer p, .index i | .index i, .pointer p => p.advance i
    | .index i, .index j => return .index (i+j)
    | _, _ => throw "pointer view: invalid addition"
  | .sub x y => do
    let i ← indexValue (← eval allocations env y)
    match ← eval allocations env x with
    | .pointer p => p.advance (-i)
    | .index j => return .index (j-i)
    | _ => throw "pointer view: invalid subtraction"

private def remote (p : Pointer) (r : CellRange) (peer : Nat) : Except String CellRange := do
  let some addr := symmAt (fun _ => p.allocation.symmetric) r.first peer
    | throw "pointer view: remote endpoint requires symmetric global storage"
  return { r with first := addr }

/-- Project a source fragment using its actual argument provenance and lane indices.
A buffer's declared unit is checked on *every* access, including through aliases. -/
def project (launch : Launch) (code : List Instruction) : Except String (List Access) := do
  let allocations := (launch.pointers.map (·.allocation)).eraseDups
  let mut env : List (String × Operand) := launch.integers.map fun (n,i) => (n,.index i)
  unless ((env.map Prod.fst ++ launch.pointers.map (·.name)).Nodup) do
    throw "pointer view: duplicate argument"
  for a in allocations do
    let w ← byteWidth a.unit
    unless a.baseByte % w == 0 && a.extentBytes % w == 0 do
      throw "pointer view: allocation is not aligned to its cell unit"
    if allocations.any (fun b => b != a && b.space == a.space && b.region == a.region) then
      throw "pointer view: inconsistent allocation for aliased arguments"
    if allocations.any (fun b => b != a && b.space == a.space &&
        max a.baseByte b.baseByte < min (a.baseByte + a.extentBytes) (b.baseByte + b.extentBytes)) then
      throw "pointer view: distinct allocations overlap in one address space"
  for arg in launch.pointers do
    let p : Pointer := ⟨arg.allocation, 0, some arg.declared⟩
    env := (arg.name, .pointer (← p.checkAlignment)) :: env
  let mut accesses := #[]
  for instruction in code do
    let value := eval allocations env
    let ptr := fun e => value e >>= ptrValue
    match instruction with
    | .assign name e => env := (name, ← value e) :: env
    | .load name e =>
      let (dtype, range) ← (← ptr e).dereference
      accesses := accesses.push (.read dtype range)
      env := (name,.payload) :: env
    | .store e v =>
      -- A stored value cannot contribute a hidden memory operation to this projection.
      match ← value v with
      | .pointer _ => throw "pointer view: storing pointer values is unsupported"
      | _ => pure ()
      let (dtype, range) ← (← ptr e).dereference
      accesses := accesses.push (.write dtype range)
    | .wait signal cmp target =>
      let p ← ptr signal
      unless p.pointee == some .i64 || p.pointee == some .u64 do
        throw "signal wait: expected an int64 or uint64 pointer"
      unless p.allocation.unit == .i64 || p.allocation.unit == .u64 do
        throw "signal wait: expected int64 or uint64 storage"
      let word ← p.range 8
      let rhs ← indexValue (← value target)
      unless -(2^63) ≤ rhs && rhs < 2^64 do
        throw "signal wait: target outside int64 and uint64 ranges"
      accesses := accesses.push (.wait ⟨word.first, p.allocation.unit == .i64, cmp, BitVec.ofInt 64 rhs⟩)
    | .transfer put d s n rank =>
      let dst ← ptr d
      let src ← ptr s
      unless dst.allocation.unit == src.allocation.unit do
        throw "pointer view: cell transfers require the same dtype at both endpoints"
      let bytes ← natIndex (← indexValue (← value n))
      let peer ← natIndex (← indexValue (← value rank))
      let dr ← dst.range bytes
      let sr ← src.range bytes
      if put then accesses := accesses.push (.put (← remote dst dr peer) sr)
      else accesses := accesses.push (.get dr (← remote src sr peer))
  return accesses.toList

declare_syntax_cat viewExpr
declare_syntax_cat viewTarget
declare_syntax_cat viewStmt

scoped syntax:max ident : viewExpr
scoped syntax:max num : viewExpr
scoped syntax:max "(" viewExpr ")" : viewExpr
scoped syntax:65 viewExpr:65 "+" viewExpr:66 : viewExpr
scoped syntax:65 viewExpr:65 "-" viewExpr:66 : viewExpr
scoped syntax:70 viewExpr:70 "*" viewExpr:71 : viewExpr
scoped syntax "tl.pointer_type(" tritonDType ")" : viewTarget
scoped syntax "tl.pointer_type(" ident ")" : viewTarget
scoped syntax ident : viewTarget
scoped syntax (name := castPtr) "tl.cast(" viewExpr "," (&"dtype" "=")? viewTarget
  ("," &"_semantic" "=" &"_semantic")? ")" : viewExpr
scoped syntax (name := methodPtr) ident noWs "(" viewTarget ")" : viewExpr
scoped syntax ident "=" viewExpr : viewStmt
scoped syntax ident "+=" viewExpr : viewStmt
scoped syntax ident "=" "tl.load(" viewExpr ")" : viewStmt
scoped syntax "tl.store(" viewExpr "," viewExpr ")" : viewStmt
scoped syntax ident "(" viewExpr "," viewExpr "," viewExpr "," viewExpr ")" : viewStmt
scoped syntax (name := signalWaitCall) ident "(" viewExpr "," ident "," viewExpr ","? ")" : viewStmt

private def targetTerm (stx : TSyntax `viewTarget) : MacroM Term := do
  match stx with
  | `(viewTarget| $a:ident) =>
    unless a.getId == `pi_u64_t do Macro.throwErrorAt a "pointer view: unsupported pointer alias"
    `(some SourceDType.u64)
  | `(viewTarget| tl.pointer_type($d:ident)) =>
    unless d.getId == `tl.void do Macro.throwErrorAt d "pointer view: unsupported pointee dtype"
    `(none)
  | `(viewTarget| tl.pointer_type($d:tritonDType)) =>
    let name := d.raw[0].getAtomVal.toName
    let entries : List (SourceDType × Name) := [
      (.i8, ``SourceDType.i8), (.i16, ``SourceDType.i16), (.i32, ``SourceDType.i32),
      (.i64, ``SourceDType.i64), (.u8, ``SourceDType.u8), (.u16, ``SourceDType.u16),
      (.u32, ``SourceDType.u32), (.u64, ``SourceDType.u64), (.fp16, ``SourceDType.fp16),
      (.bf16, ``SourceDType.bf16), (.fp32, ``SourceDType.fp32), (.fp64, ``SourceDType.fp64),
      (.f8e4, ``SourceDType.f8e4), (.f8e5, ``SourceDType.f8e5)]
    let some (_, ctor) := entries.find? (fun (t,_) => VeriTile.Triton.DSL.SourceDType.dtypeName t == name)
      | Macro.throwErrorAt d "pointer view: unsupported pointee dtype"
    let t := mkIdent ctor
    `(some $t)
  | _ => Macro.throwErrorAt stx "pointer view: unsupported pointer target"

private partial def exprTerm (e : TSyntax `viewExpr) : MacroM Term := do
  match e with
  | `(viewExpr| $n:num) => `(AddressExpr.literal $n)
  | `(viewExpr| $x:ident) => do
    let key := quote x.getId.toString
    `(AddressExpr.var $key)
  | `(viewExpr| ($v:viewExpr)) => exprTerm v
  | `(viewExpr| $x:viewExpr + $y:viewExpr) => do
    let a ← exprTerm x
    let b ← exprTerm y
    `(AddressExpr.add $a $b)
  | `(viewExpr| $x:viewExpr - $y:viewExpr) => do
    let a ← exprTerm x
    let b ← exprTerm y
    `(AddressExpr.sub $a $b)
  | `(viewExpr| $x:viewExpr * $y:viewExpr) => do
    let a ← exprTerm x
    let b ← exprTerm y
    `(AddressExpr.mul $a $b)
  | `(viewExpr| $fn:ident($t:viewTarget)) =>
    let .str name "to" := fn.getId | Macro.throwErrorAt fn "pointer view: expected a .to method"
    let key := quote name.toString
    let dtype ← targetTerm t
    `(AddressExpr.cast (.var $key) $dtype)
  | _ =>
    if e.raw.isOfKind ``castPtr then
      let v ← exprTerm ⟨e.raw[1]⟩
      let t ← targetTerm ⟨e.raw[4]⟩
      `(AddressExpr.cast $v $t)
    else Macro.throwErrorAt e "pointer view: unsupported address expression"

private def stmtTerm (s : TSyntax `viewStmt) : MacroM Term := do
  if s.raw.isOfKind ``signalWaitCall then
    let fn := s.raw[0]
    unless fn.getId == `libshmem_device.signal_wait_until do
      Macro.throwErrorAt fn "pointer view: unsupported three-argument call"
    let op := s.raw[4]
    let name ← match op.getId with
      | `libshmem_device.NVSHMEM_CMP_EQ => pure ``Cmp.eq
      | `libshmem_device.NVSHMEM_CMP_NE => pure ``Cmp.ne
      | `libshmem_device.NVSHMEM_CMP_GT => pure ``Cmp.gt
      | `libshmem_device.NVSHMEM_CMP_LE => pure ``Cmp.le
      | `libshmem_device.NVSHMEM_CMP_LT => pure ``Cmp.lt
      | `libshmem_device.NVSHMEM_CMP_GE => pure ``Cmp.ge
      | _ => Macro.throwErrorAt op "signal wait: unsupported comparison"
    let p ← exprTerm ⟨s.raw[2]⟩
    let target ← exprTerm ⟨s.raw[6]⟩
    let op := mkIdent name
    return ← `(Instruction.wait $p $op $target)
  match s with
  | `(viewStmt| $n:ident = tl.load($e:viewExpr)) =>
    let key := quote n.getId.toString
    let value ← exprTerm e
    `(Instruction.load $key $value)
  | `(viewStmt| tl.store($e:viewExpr, $v:viewExpr)) =>
    let address ← exprTerm e
    let val ← exprTerm v
    `(Instruction.store $address $val)
  | `(viewStmt| $n:ident = $e:viewExpr) =>
    let key := quote n.getId.toString
    let value ← exprTerm e
    `(Instruction.assign $key $value)
  | `(viewStmt| $n:ident += $e:viewExpr) =>
    let key := quote n.getId.toString
    let val ← exprTerm e
    `(Instruction.assign $key (.add (.var $key) $val))
  | `(viewStmt| $fn:ident($d:viewExpr, $src:viewExpr, $n:viewExpr, $r:viewExpr)) =>
    let name := fn.getId.toString
    let puts := ["libshmem_device.putmem_block", "libshmem_device.putmem_nbi_block"]
    let gets := ["libshmem_device.getmem_block", "libshmem_device.getmem_nbi_block"]
    unless (puts ++ gets).contains name do Macro.throwErrorAt fn "pointer view: unsupported transfer"
    let put := quote (puts.contains name)
    let dst ← exprTerm d
    let source ← exprTerm src
    let count ← exprTerm n
    let peer ← exprTerm r
    `(Instruction.transfer $put $dst $source $count $peer)
  | _ => Macro.throwErrorAt s "pointer view: unsupported address statement"

scoped syntax "with_pointer_views " term " in " "triton " "{" viewStmt* "}" : term
macro_rules
  | `(with_pointer_views $bindings:term in triton { $statements:viewStmt* }) => do
    let code ← statements.mapM stmtTerm
    `(project $bindings [$code,*])

-- Delegate value casts to the actual compute frontend. It checks supported source
-- and destination pairs and supplies the existing numeric or bit-pattern semantics.
scoped syntax (name := numericKw) "tl.cast(" tritonExpr "," &"dtype" "=" tritonDType ")" : tritonExpr
declare_syntax_cat castFlag
scoped syntax "bitcast=True" : castFlag
scoped syntax ident "=" "true" : castFlag
scoped syntax ident "=" "false" : castFlag
scoped syntax ident "=" ident : castFlag
scoped syntax (name := bitKw) "tl.cast(" tritonExpr "," (&"dtype" "=")? tritonDType ","
  castFlag ")" : tritonExpr

private partial def valueCasts (raw : Syntax) : MacroM Syntax := do
  let raw := raw.setArgs (← raw.getArgs.mapM valueCasts)
  if raw.isOfKind ``numericKw then
    let v : TSyntax `tritonExpr := ⟨raw[1]⟩
    let t : TSyntax `tritonDType := ⟨raw[5]⟩
    return (← `(tritonExpr| tl.cast($v, $t))).raw
  if raw.isOfKind ``bitKw then
    let v : TSyntax `tritonExpr := ⟨raw[1]⟩
    let t : TSyntax `tritonDType := ⟨raw[4]⟩
    let flag := raw[6]
    if flag.getNumArgs != 1 && flag[0].getId != `bitcast then
      Macro.throwErrorAt flag "tl.cast: expected bitcast keyword"
    let name := if flag.getNumArgs == 1 then "True" else if flag[2].isAtom then
      flag[2].getAtomVal else flag[2].getId.toString
    match name with
    | "True" | "true" => return (← `(tritonExpr| tl.bitcast($v, $t))).raw
    | "False" | "false" => return (← `(tritonExpr| tl.cast($v, $t))).raw
    | _ => Macro.throwErrorAt flag "tl.cast: bitcast must be a literal Boolean"
  return raw

@[term_elab VeriTile.Triton.DSL.tritonBlock] def elaborateValueCasts : Elab.Term.TermElab := fun stx expected => do
  let normalized ← liftMacroM (valueCasts stx)
  if normalized == stx then throwUnsupportedSyntax
  Elab.Term.elabTerm normalized expected

end VeriTile.Dist.Frontend.TritonExt.PointerCasts
