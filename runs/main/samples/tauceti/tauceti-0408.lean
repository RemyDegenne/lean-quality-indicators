public section

namespace TauCeti

open Complex Filter MeasureTheory Topology

open scoped Real

variable {x c : ℝ}

@[simp]
theorem perronIntegrand_zero (hc : c ≠ 0) (t : ℝ) : perronIntegrand 0 c t = 0 := by
  have hline : (c : ℂ) + t * I ≠ 0 := fun h ↦ hc (by simpa using congrArg Complex.re h)
  rw [perronIntegrand_def, Complex.ofReal_zero, Complex.zero_cpow hline, zero_div]

end TauCeti
end
