import tests.lean.TileLangPinnedRoots

/-! Reconstruct Python from the public typed object. The checker compares CPython ASTs
with the original source spans, independently of the quotation printer and parser. -/
namespace VeriTile.TileLang.TypedRoundTrip

private def comma (xs : List String) := String.intercalate ", " xs
private def quoted (s : String) := (Lean.Json.str s).compress
private def pyBool (b : Bool) := if b then "True" else "False"
private def tuple (xs : List String) :=
  "(" ++ comma xs ++ (if xs.length == 1 then "," else "") ++ ")"

private def binary : Binary → String
  | .pow => "**" | .mul => "*" | .div => "/" | .floorDiv => "//" | .mod => "%"
  | .add => "+" | .sub => "-" | .xor => "^" | .lt => "<" | .gt => ">"
  | .le => "<=" | .ge => ">=" | .eq => "==" | .ne => "!=" | .and => "and" | .or => "or"

mutual
private partial def value : Value → String
  | .ident n => n.toString
  | .integer n => toString n
  | .decimal s => s
  | .string s => quoted s
  | .boolean b => pyBool b
  | .tuple xs => tuple (xs.map value)
  | .list xs => "[" ++ comma (xs.map value) ++ "]"
  | .index n xs => n.toString ++ "[" ++ comma (xs.map coord) ++ "]"
  | .neg x => "(-" ++ value x ++ ")"
  | .not x => "(not " ++ value x ++ ")"
  | .binary op x y => "(" ++ value x ++ " " ++ binary op ++ " " ++ value y ++ ")"
  | .conditional y c n => "(" ++ value y ++ " if " ++ value c ++ " else " ++ value n ++ ")"
  | .call n args => n.toString ++ "(" ++ comma (args.map arg) ++ ")"
  | .layout s ns m => "T.Layout(" ++ value s ++ ", lambda " ++ comma (ns.map toString) ++ ": " ++ value m ++ ")"
  | .layoutMap n l => "{" ++ n.toString ++ ": " ++ value l ++ "}"
private partial def arg : Argument → String
  | .pos v => value v
  | .keyword n v => n.toString ++ "=" ++ value v
private partial def coord : Index → String
  | .atIndex v => value v
  | .slice lo hi => (lo.map value).getD "" ++ ":" ++ (hi.map value).getD ""
end

private def place : Place → String
  | .variable n => n.toString
  | .index n xs => n.toString ++ "[" ++ comma (xs.map coord) ++ "]"
  | .unpack ns => comma (ns.map toString)

private def tensor (n : Lean.Name) (s d : Value) :=
  n.toString ++ ": T.Tensor(" ++ value s ++ ", " ++ value d ++ ")"

private def param : Parameter → String
  | .required n => n.toString
  | .optional n v => n.toString ++ "=" ++ value v
  | .tensor n s d => tensor n s d

private def indent (s : String) :=
  String.intercalate "\n" ((s.splitOn "\n").map ("    " ++ ·))

private def block (header : String) (body : List String) :=
  header ++ ":\n" ++ indent (String.intercalate "\n" body)

private partial def stmt : Statement → String
  | .assign p v => place p ++ " = " ++ value v
  | .annotate n s d => tensor n s d
  | .update p op v => place p ++ " " ++ binary op ++ "= " ++ value v
  | .invoke n args => n.toString ++ "(" ++ comma (args.map arg) ++ ")"
  | .ret v => "return " ++ value v
  | .branch c y n => block ("if " ++ value c) (y.map stmt) ++
      (if n.isEmpty then "" else "\n" ++ block "else" (n.map stmt))
  | .loop ns it args body => block ("for " ++ comma (ns.map toString) ++ " in " ++
      it.toString ++ "(" ++ comma (args.map arg) ++ ")") (body.map stmt)
  | .kernel args ns body => block ("with T.Kernel(" ++ comma (args.map arg) ++ ") as " ++
      (if ns.length == 1 then comma (ns.map toString) else tuple (ns.map toString))) (body.map stmt)
  | .role v body => block ("with T.ws(" ++ value v ++ ")") (body.map stmt)
  | .assertStatic c msg => "assert " ++ value c ++ (msg.map (fun s => ", " ++ quoted s)).getD ""
  | .whileLoop c body => block ("while " ++ value c) (body.map stmt)
  | .breakLoop => "break"
  | .continueLoop => "continue"

private def proc (p : Procedure) (afterBody : List String := []) :=
  block ("def " ++ p.name.toString ++ "(" ++ comma (p.params.map param) ++ ")")
    (p.body.map stmt ++ afterBody)

private def helper (h : LayoutHelper) :=
  block ("def " ++ h.name.toString ++ "(" ++ h.param.toString ++ ")")
    ["return " ++ value (.layout h.shape h.coordinates h.mapping)]

private def jitOption : JitOption → String
  | .outputs ns => "out_idx=[" ++ comma (ns.map toString) ++ "]"
  | .flag k b =>
    let key := match k with
      | .literal s => quoted s
      | .symbol n => n.toString
    "pass_configs={" ++ key ++ ": " ++ pyBool b ++ "}"

private def program (p : Program) : String := Id.run do
  let dec := match p.jit with
    | none => ""
    | some [] => "@tilelang.jit\n"
    | some opts => "@tilelang.jit(" ++ comma (opts.map jitOption) ++ ")\n"
  let body := match p.definition with
    | .direct f => proc f
    | .factory f macros prim ret =>
      proc f (macros.map (fun m => "@T.macro\n" ++ proc m) ++
        ["@T.prim_func\n" ++ proc prim, "return " ++ ret.toString])
  return String.intercalate "\n" (p.layouts.map helper ++ [dec ++ body])

def render (p : Program) : Lean.Json := Lean.Json.str (program p)
end VeriTile.TileLang.TypedRoundTrip

def main : IO Unit := do
  let json := Lean.Json.arr (VeriTile.TileLang.PinnedRoots.programs.map
    VeriTile.TileLang.TypedRoundTrip.render).toArray
  IO.println json.compress
