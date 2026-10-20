public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric TopologicalSpace

open scoped RealInnerProductSpace

variable {n : ℕ}

theorem ballGreenCorrector_eq_newtonianKernel {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    ballGreenCorrector n x y = newtonianKernel n (‖x‖ • y - ‖x‖⁻¹ • x) := by
  rw [ballGreenCorrector_def, newtonianKernel_def,
    ← norm_sq_norm_smul_sub_inv_norm_smul (norm_ne_zero_iff.mpr hx) y,
    norm_rpow_eq_norm_sq_rpow]

end TauCeti
end
end
