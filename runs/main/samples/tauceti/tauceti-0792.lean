public section

noncomputable section

open Complex Metric

namespace TauCeti.Contour

theorem windingNumber_circle {c : ℂ} {r : ℝ} (hr : r ≠ 0) : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (circleMap c r) θ / (circleMap c r θ - c)
      = 1 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [indexIntegral_arc hr]
  push_cast
  field_simp

end TauCeti.Contour
end
end
