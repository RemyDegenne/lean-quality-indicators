@[expose] public section

namespace LeanPool.LeanComplexAnalysis

open Real Complex InnerProductSpace MeasureTheory Metric Set Topology

/-- The linear map `ΛNLinear`. -/
noncomputable def ΛNLinear (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ)
    (h : Continuous (uN p r n ∘ circleMap 0 1)) : CUnitCircle →ₗ[ℝ] ℝ where
  toFun f := ΛNVal p r n f
  map_add' f g := by
    unfold ΛNVal
    simp only [one_div, mul_inv_rev, ContinuousMap.add_apply, add_mul]
    rw [← mul_add, intervalIntegral.integral_add]
    · apply_rules [Continuous.intervalIntegrable]
      exact Continuous.mul (f.continuous.comp <| by continuity) h
    · apply_rules [Continuous.intervalIntegrable]
      exact Continuous.mul (g.continuous.comp <| by continuity) h
  map_smul' c f := by
    unfold ΛNVal
    simp [mul_assoc, mul_left_comm, ← intervalIntegral.integral_const_mul]

end LeanPool.LeanComplexAnalysis
end
