import VeriTile.TileLang

open Lean VeriTile.TileLang
namespace TileLangManualAcceptance

private def one : Value := .integer 1
private def binding (v : Value) : Statement := .assign (.variable `x) v
private def launch (ss : List Statement) : Statement := .kernel [.pos one] [`b] ss
private def direct (body : List Statement) (name := `outer) : Program :=
  ⟨.tileLang, [], some [], .direct ⟨name, [], [launch body, .ret one]⟩⟩
private def factory (outer := `outer) (macros : List Procedure := [])
    (body := [launch [binding one]]) : Program :=
  ⟨.tileLang, [], none, .factory ⟨outer, [], []⟩ macros ⟨`inner, [], body⟩ `inner⟩
private def helper : LayoutHelper := ⟨`layout, `A, .ident `A.shape, [`i], .ident `i⟩

-- Each bad object differs from an accepted object in a single field.
example : (direct [binding (.call `T.exp2 [.pos one])]).accepted = true := by with_unfolding_all rfl
example : (direct [binding (.call `T.sqrt [.pos one])]).accepted = false := by with_unfolding_all rfl
example : (direct [binding (.call `T.sqrt [.pos one, .pos one])]).accepted = false := by with_unfolding_all rfl
example : (direct [binding (.call `T.sqrt [.pos one, .pos one, .pos one])]).accepted = false := by with_unfolding_all rfl
example : ({ factory `outer with layouts := [helper] } : Program).accepted = true := by with_unfolding_all rfl
example : ({ factory `outer with layouts := [{helper with shape := .ident `B.shape}] } : Program).accepted = false := by with_unfolding_all rfl
example : (factory `outer).accepted = true := by with_unfolding_all rfl
example : (factory `inner).accepted = false := by with_unfolding_all rfl
example : ({factory `layout with layouts := [helper]} : Program).accepted = false := by with_unfolding_all rfl
example : (factory `if).accepted = false := by with_unfolding_all rfl
example : (direct [binding one]).accepted = true := by with_unfolding_all rfl
example : (direct [binding one] `if).accepted = false := by with_unfolding_all rfl
example : (factory `outer [] []).accepted = false := by with_unfolding_all rfl
example : ({factory `outer with layouts := [{helper with name := `inner}]} : Program).accepted = false := by with_unfolding_all rfl
example : (direct []).accepted = false := by with_unfolding_all rfl
example : ({direct [binding one] with jit := none} : Program).accepted = false := by with_unfolding_all rfl
example : ({direct [binding one] with jit := some [.outputs [0]]} : Program).accepted = true := by with_unfolding_all rfl
example : ({direct [binding one] with jit := some [.outputs []]} : Program).accepted = false := by with_unfolding_all rfl
example : (direct [.update (.variable `x) .add one]).accepted = true := by with_unfolding_all rfl
example : (direct [.update (.variable `x) .mod one]).accepted = false := by with_unfolding_all rfl
example : (factory `outer [⟨`work, [], [binding one]⟩]).accepted = true := by with_unfolding_all rfl
example : (factory `outer [⟨`work, [], []⟩]).accepted = false := by with_unfolding_all rfl

end TileLangManualAcceptance
