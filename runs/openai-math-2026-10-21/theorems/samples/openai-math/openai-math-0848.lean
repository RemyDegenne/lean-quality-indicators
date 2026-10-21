namespace OAI

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem finiteFourierSum_bound (frequency : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    ‖finiteFourierSum frequency a t‖ ≤ ∑ i, ‖a i‖ := by
  unfold finiteFourierSum
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_mul, norm_character, mul_one]

end LipschitzHilbert.PhaseCombinatorics
end
end OAI
