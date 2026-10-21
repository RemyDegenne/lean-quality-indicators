namespace OAI

namespace BackwardIntertwiners

open Filter

open scoped Topology

noncomputable section

open Topology MeasureTheory Set

open scoped ENNReal

lemma fiberMultiplier_mem {a : ℤ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) (v : Fiber) : Memℓp (fun j => a j*v j) 2 := by
  apply ((lp.memℓp v).const_smul (C:ℂ)).mono'
  intro j
  simp only [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hC, norm_mul]
  exact mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _)

end
end BackwardIntertwiners
end OAI
