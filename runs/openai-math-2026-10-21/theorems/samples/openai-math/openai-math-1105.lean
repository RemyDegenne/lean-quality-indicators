namespace OAI

noncomputable section

open Polynomial

namespace InternalCatalan

theorem fixed_reversedT_typed_tail_1 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_1 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_1, ite_eq_right]

end InternalCatalan
end
end OAI
