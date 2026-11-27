import Lean

/-! Typed source categories of the TileLang quotation. Source expressions retain the
symbolic extents and dtype names which are resolved by operator contracts. -/
namespace VeriTile.TileLang
open Lean

inductive Mode where | tileLang | tileScale
  deriving Repr, BEq, ToExpr, Inhabited

inductive Binary where
  | pow | mul | div | floorDiv | mod | add | sub | xor | lt | gt | le | ge | eq | ne | and | or
  deriving Repr, BEq, ToExpr, Inhabited

mutual
inductive Value where
  | ident (id : Name)
  | integer (n : Nat)
  | decimal (spelling : String)
  | string (s : String)
  | boolean (b : Bool)
  | tuple (xs : List Value)
  | list (xs : List Value)
  | index (buffer : Name) (coords : List Index)
  | neg (x : Value)
  | not (x : Value)
  | binary (op : Binary) (x y : Value)
  | conditional (yes condition no : Value)
  | call (callee : Name) (args : List Argument)
  | layout (shape : Value) (coordinates : List Name) (mapping : Value)
  | layoutMap (buffer : Name) (layout : Value)
  deriving Repr, BEq, ToExpr, Inhabited
inductive Argument where
  | pos (value : Value)
  | keyword (key : Name) (value : Value)
  deriving Repr, BEq, ToExpr, Inhabited
inductive Index where
  | atIndex (value : Value)
  | slice (start stop : Option Value)
  deriving Repr, BEq, ToExpr, Inhabited
end

inductive Place where
  | variable (id : Name)
  | index (buffer : Name) (coords : List Index)
  | unpack (names : List Name)
  deriving Repr, BEq, ToExpr, Inhabited

inductive Parameter where
  | required (id : Name)
  | optional (id : Name) (value : Value)
  | tensor (id : Name) (shape dtype : Value)
  deriving Repr, BEq, ToExpr, Inhabited

inductive Statement where
  | assign (dst : Place) (value : Value)
  | annotate (name : Name) (shape dtype : Value)
  | update (dst : Place) (op : Binary) (value : Value)
  | invoke (callee : Name) (args : List Argument)
  | ret (value : Value)
  | branch (condition : Value) (yes no : List Statement)
  | loop (binders : List Name) (iterator : Name) (args : List Argument) (body : List Statement)
  | kernel (grid : List Argument) (binders : List Name) (body : List Statement)
  | role (number : Value) (body : List Statement)
  | assertStatic (condition : Value) (message : Option String)
  | whileLoop (condition : Value) (body : List Statement)
  | breakLoop | continueLoop
  deriving Repr, BEq, ToExpr, Inhabited

structure Procedure where
  name : Name
  params : List Parameter
  body : List Statement
  deriving Repr, BEq, ToExpr, Inhabited

structure LayoutHelper where
  name : Name
  param : Name
  shape : Value
  coordinates : List Name
  mapping : Value
  deriving Repr, BEq, ToExpr, Inhabited

inductive OptionKey where
  | literal (key : String)
  | symbol (name : Name)
  deriving Repr, BEq, ToExpr, Inhabited

inductive JitOption where
  | outputs (indices : List Nat)
  | flag (key : OptionKey) (value : Bool)
  deriving Repr, BEq, ToExpr, Inhabited

inductive Definition where
  | direct (function : Procedure)
  | factory (function : Procedure) (macros : List Procedure) (primFunc : Procedure) (returned : Name)
  deriving Repr, BEq, ToExpr, Inhabited

structure Program where
  mode : Mode
  layouts : List LayoutHelper
  /-- None distinguishes an undecorated factory from a JIT decorator without options. -/
  jit : Option (List JitOption)
  definition : Definition
  deriving Repr, BEq, ToExpr, Inhabited

/-- The literal option selected by the source, with absence distinct from false. -/
def Program.fastMath (p : Program) : Option Bool :=
  (p.jit.getD []).findSome? fun
    | .flag (.symbol `tilelang.PassConfigKey.TL_ENABLE_FAST_MATH) b => some b
    | _ => none

end VeriTile.TileLang
