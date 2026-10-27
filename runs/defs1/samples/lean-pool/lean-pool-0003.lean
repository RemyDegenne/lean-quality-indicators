@[expose] public section

open Filter MeasureTheory Set

open scoped ENNReal NNReal Topology

namespace QuadraticCarleson

namespace L0Infinity

/-- Complex scalar multiplication on the paper's test-function space. -/
noncomputable def smul (c : ℂ) (f : L0Infinity) : L0Infinity where
  toFun := fun x ↦ c * f x
  measurable_toFun := measurable_const.mul f.measurable_toFun
  bounded_toFun := by
    rcases f.bounded_toFun with ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun x ↦ ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
  hasCompactSupport_toFun := by
    exact f.hasCompactSupport_toFun.comp_left (mul_zero c)

end L0Infinity
end QuadraticCarleson
end
