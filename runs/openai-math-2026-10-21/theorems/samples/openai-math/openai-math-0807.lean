namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.SparseContact

open scoped BigOperators Classical

lemma mixedReturn_eq_iff {L : Type*} (d : ℕ) (A : Finset L)
    (ω : Option L → (SwitchIndex d → Bool)) (y z : L → Card d) :
    mixedReturn d A ω y = z ↔ mixedTuple d A ω z = y := by
  constructor
  · intro h
    funext i
    exact (Equiv.symm_apply_eq _).mp (congrFun h i) |>.symm
  · intro h
    funext i
    exact (Equiv.symm_apply_eq _).mpr (congrFun h i).symm

end Thorp.SparseContact
end ThorpNine.Adaptive
end OAI
