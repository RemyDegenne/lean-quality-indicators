public section

noncomputable section

open Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

theorem continuousOn_schwarzChristoffelBoundary_Iic (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p : ℝ} (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → p ≤ a i) :
    ContinuousOn (schwarzChristoffelBoundary a e z₀) (Iic p) := by
  apply continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one
  intro x hx
  exact Finset.lt_sum_filter_of_lt_zero_of_forall_ne_zero_le (γ := OrderDual ℝ)
    Finset.univ (by norm_num) hp (fun i _ hi => ha i hi) hx

end TauCeti
end
end
