namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem centered_product_mean_abs_le {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (hS : S.Nonempty) (F : I → X → ℝ) {error : ℝ}
    (hmean : ∀ U ⊆ S, |(𝔼 x, ∏ i ∈ U, F i x) - 1| ≤ error) :
    |𝔼 x, ∏ i ∈ S, (F i x - 1)| ≤ (2 : ℝ) ^ S.card * error := by
  rw [centered_product_mean_expansion S hS F]
  calc
    _ ≤ ∑ U ∈ S.powerset,
        |(-1 : ℝ) ^ U.card * ((𝔼 x, ∏ i ∈ S \ U, F i x) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _U ∈ S.powerset, error := by
      apply Finset.sum_le_sum
      intro U _
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hmean (S \ U) Finset.sdiff_subset
    _ = _ := by simp

end Erdos3
end
end OAI
