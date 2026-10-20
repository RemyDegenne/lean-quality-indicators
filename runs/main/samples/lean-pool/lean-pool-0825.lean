section

@[expose] public section

noncomputable section

open Set Function Filter MeasureTheory

open scoped BigOperators ContDiff Topology

namespace NavierStokes.AngularMomentReset

theorem angular_weight_formula (lam e0 X0 y : ℝ) (hX : 0 ≤ X0) :
    radiusX X0 y * baseH lam e0 X0 y =
      X0 * Real.sqrt (2 * X0) * e0 * Real.exp (angularSlope lam * y) := by
  have hs : Real.sqrt (2 * radiusX X0 y) = Real.sqrt (2 * X0) * Real.exp (y / 2) := by
    unfold radiusX
    rw [← mul_assoc, Real.sqrt_mul (by positivity), sqrt_exp_half]
  unfold baseH
  rw [hs]
  unfold radiusX baseE
  calc
    _ = X0 * Real.sqrt (2 * X0) * e0 *
        (Real.exp y * Real.exp (y / 2) * Real.exp ((-1 / 2 - lam) * y)) := by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      unfold angularSlope
      ring

end NavierStokes.AngularMomentReset
end
end
end
