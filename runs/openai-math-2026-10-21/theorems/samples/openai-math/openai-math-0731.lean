namespace OAI

section

namespace BinaryMatching.RecursiveEval

open StackCode

variable {A B C P : Type}

namespace Compile

open StackCode.Poly

variable [Coding A] [Coding B] [Coding C] [Coding P]
  [Inhabited A] [Inhabited B] [Inhabited C]

@[fun_prop] theorem execCommand_poly (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (hz : Poly zero)
    (he : Poly (fun z : P×A => expand z.1 z.2))
    (hc : Poly (fun z : P×(C×(B×B)) => combine z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Poly (execCommand zero expand combine) := by
  unfold execCommand
  apply commandCasesWith Prod.snd
    (fun z : ((P×State A B C)×Command A C)×(ℕ×A) =>
      if z.2.1=0 then (z.1.1.2.1.tail,zero z.1.1.1::z.1.1.2.2) else
      match expand z.1.1.1 z.2.2 with
      | .leaf b => (z.1.1.2.1.tail,b::z.1.1.2.2)
      | .fork c x y => (.call (z.2.1-1) x::.call (z.2.1-1) y::.join c::z.1.1.2.1.tail,z.1.1.2.2))
    (fun z => if 2≤z.1.1.2.2.length then
      (z.1.1.2.1.tail,combine z.1.1.1 z.2 (z.1.1.2.2.tail.headD default) (z.1.1.2.2.headD default)::z.1.1.2.2.tail.tail)
      else ([],z.1.1.2.2))
  · fun_prop
  · have hb₀ := branchCasesWith
      (fun z : ((P×State A B C)×Command A C)×(ℕ×A) => expand z.1.1.1 z.2.2)
      (fun z => (z.1.1.1.2.1.tail,z.2::z.1.1.1.2.2))
      (fun z => (Command.call (z.1.2.1-1) z.2.2.1::Command.call (z.1.2.1-1) z.2.2.2::
        Command.join z.2.1::z.1.1.1.2.1.tail,z.1.1.1.2.2))
      (by fun_prop) (by fun_prop) (by fun_prop)
    have hb : Poly (fun z : ((P×State A B C)×Command A C)×(ℕ×A) =>
        match expand z.1.1.1 z.2.2 with
        | .leaf b => (z.1.1.2.1.tail,b::z.1.1.2.2)
        | .fork c x y => (.call (z.2.1-1) x::.call (z.2.1-1) y::.join c::z.1.1.2.1.tail,z.1.1.2.2)) :=
      hb₀.congr (fun z => by cases expand z.1.1.1 z.2.2 <;> rfl)
    have h : Poly (fun z : ((P×State A B C)×Command A C)×(ℕ×A) =>
        if decide (z.2.1=0) then (z.1.1.2.1.tail,zero z.1.1.1::z.1.1.2.2) else
        match expand z.1.1.1 z.2.2 with
        | .leaf b => (z.1.1.2.1.tail,b::z.1.1.2.2)
        | .fork c x y => (.call (z.2.1-1) x::.call (z.2.1-1) y::.join c::z.1.1.2.1.tail,z.1.1.2.2)) := by fun_prop
    exact h.congr (fun _ => by simp)
  · have h : Poly (fun z : ((P×State A B C)×Command A C)×C => if decide (2≤z.1.1.2.2.length) then
        (z.1.1.2.1.tail,combine z.1.1.1 z.2 (z.1.1.2.2.tail.headD default) (z.1.1.2.2.headD default)::z.1.1.2.2.tail.tail)
        else ([],z.1.1.2.2)) := by fun_prop
    exact h.congr (fun _ => by simp)

end Compile
end BinaryMatching.RecursiveEval
end
end OAI
