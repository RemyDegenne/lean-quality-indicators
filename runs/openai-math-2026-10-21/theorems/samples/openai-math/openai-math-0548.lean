namespace OAI

namespace ThorpNine.Smoothing

namespace Thorp

open scoped BigOperators

open Filter

namespace CycleColoring

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
lemma alternatingPerm_flip (p : Equiv.Perm α) (x : Bool × α) :
    (alternatingPerm p x).1 = !x.1 := by
  rcases x with ⟨b,x⟩
  cases b <;> rfl

end CycleColoring
end Thorp
end ThorpNine.Smoothing
end OAI
