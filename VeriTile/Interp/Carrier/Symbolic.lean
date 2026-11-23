import VeriTile.Interp.Algebra
import VeriTile.Triton.Float.TermModel

namespace VeriTile.Interp.Symbolic
open VeriTile.Triton VeriTile.Triton.FP VeriTile.Triton.FP.Equational

inductive DotKind where
  | dot | dotWithOptions | dotTyped | dotAcc

/-- Scalar calls with no constructor in the upstream equational signature. -/
inductive Call where
  | fma (p : IndexComputePrecision)
  | fmaTyped (d : FloatDType)
  | atomicAdd (d : FloatDType)
  | powi (p : Option ComputeDType) (n : Int)
  | minimum (p : Option ComputeDType) (d : FloatDType)
  | divRN
  | float8E5Bits (d : FloatDType) (bits : Float8E5Bits)
  | reduction (op : ScanOp) (typed : Bool) (p : Option ComputeDType) (d : FloatDType)
      (shape : TileShape) (axis : Nat) (keepDims : Bool)
  | dot (kind : DotKind) (p : Option ComputeDType) (left right out : FloatDType)
      (options : DotOptions) (k : Nat)
  | scan (p : Option ComputeDType) (op : ScanOp) (direction : ScanDirection)
      (shape : TileShape) (axis : Nat)

/-- The upstream literal symbol carries a noncomputable real. The leaf
extension keeps its exact rational preimage and embeds additional calls. -/
inductive Atom where
  | literal (p : Option ComputeDType) (dtype : FloatDType) (value : ℚ)
  | call (op : Call) (args : List (Term Atom))

instance : Inhabited Atom := ⟨.literal none .real 0⟩

abbrev Expr := Term Atom

private def call (op : Call) (args : List Expr) : Expr := .leaf (.call op args)

private def reduce (op : ScanOp) (typed : Bool) (p : Option ComputeDType) (d : FloatDType)
    {shape : TileShape} (axis : Fin shape.length) (keep : Bool)
    (xs : TileIndex shape → Expr) (i : TileIndex (TileShape.reduceShape shape axis keep)) : Expr :=
  call (.reduction op typed p d shape axis.val keep)
    ((List.finRange _).map (reductionInputs shape axis keep xs i))

private def products {m k n : Nat} : (batch : TileShape) →
    (TileIndex (batch ++ [m,k]) → Expr) → (TileIndex (batch ++ [k,n]) → Expr) →
    TileIndex (batch ++ [m,n]) → List Expr
  | [], a, b, (row, col, _) =>
    (List.finRange k).flatMap fun j => [a (row,j,()), b (j,col,())]
  | _ :: tail, a, b, (h,i) => products tail (fun j => a (h,j)) (fun j => b (h,j)) i

/-- Output values retain their operation trees. Backends requiring a concrete
control result (e.g. float comparisons) remain absent. -/
def algebra : CAlgebra Expr where
  literal := fun p d q => .leaf (.literal p d q)
  negInf := .app .negInf []
  binary := fun p d op x y => .app (.binary p d op) [x, y]
  unary := fun p op x => .app (.unary p op) [x]
  cast := fun p s d x => .app (.cast p s d) [x]
  fromNat := fun p n => .app (.fromNat p n) []
  fromInt := fun p n => .app (.fromInt p n) []
  fp32Bits := fun b => .app (.fp32Bits b) []
  fp32Load := fun x => .app .fp32Load [x]
  fma := fun p => some fun x y z => call (.fma p) [x, y, z]
  fmaTyped := fun d => some fun x y z => call (.fmaTyped d) [x, y, z]
  atomicAdd := fun d => some fun x y => call (.atomicAdd d) [x, y]
  libdevicePowi := fun p => some fun x n => call (.powi p n) [x]
  minimum := fun p d => some fun x y => call (.minimum p d) [x, y]
  divRN := some fun x y => call .divRN [x, y]
  float8E5Bits := some fun d bits => call (.float8E5Bits d bits) []
  reduceMin := fun p _ axis keep xs => some (reduce .min false p .real axis keep xs)
  reduceMax := fun p _ axis keep xs => reduce .max false p .real axis keep xs
  reduceSum := fun p _ axis keep xs => reduce .sum false p .real axis keep xs
  reduceSumTyped := fun p d _ axis keep xs => some fun i =>
    Structural.ofFloat d (reduce .sum true p d axis keep (fun j => Structural.toFloat d (xs j)) i)
  reduceMaxTyped := fun p d _ axis keep xs => some fun i =>
    Structural.ofFloat d (reduce .max true p d axis keep (fun j => Structural.toFloat d (xs j)) i)
  scan := fun p {shape} op axis direction xs => some fun i =>
    let lane := TileShape.axisCoord shape axis i
    let lanes := match direction with
      | .forward => (List.finRange _).filter (· ≤ lane)
      | .reverse => (List.finRange _).reverse.filter (lane ≤ ·)
    call (.scan p op direction shape axis.val)
      (lanes.map fun k => xs (TileShape.replaceAxisCoord shape axis i k))
  dot := fun p {batch} {_} {k} {_} a b => some fun i =>
    call (.dot .dot p .real .real .real {} k) (products batch a b i)
  dotWithOptions := fun p opts {batch} {_} {k} {_} a b => some fun i =>
    call (.dot .dotWithOptions p .real .real .real opts k) (products batch a b i)
  dotTyped := fun p l r o opts {batch} {_} {k} {_} a b => some fun i =>
    Structural.ofFloat o (call (.dot .dotTyped p l r o opts k)
      (products batch (fun j => Structural.toFloat l (a j)) (fun j => Structural.toFloat r (b j)) i))
  dotAcc := fun p l r o opts {batch} {_} {k} {_} a b c => some fun i =>
    Structural.ofFloat o (call (.dot .dotAcc p l r o opts k)
      (Structural.toFloat o (c i) ::
        products batch (fun j => Structural.toFloat l (a j)) (fun j => Structural.toFloat r (b j)) i))

end VeriTile.Interp.Symbolic
