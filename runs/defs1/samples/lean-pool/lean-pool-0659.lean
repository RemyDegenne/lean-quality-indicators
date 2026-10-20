@[expose] public section

namespace NavierStokes.SmoothLoop

noncomputable section

open MeasureTheory

open scoped Interval ContDiff

open LoopMoments in
/-- Density of tilt, bundling `rate`, `smooth`, `positive`, `periodic` and the required
compatibility proofs. -/
def densityOfTilt (t : ℝ → ℝ) (a m ρ v : ℝ)
    (ha : 0 < a) (hv : 0 < v) (ht : ContDiff ℝ (∞ : WithTop ℕ∞) t)
    (hperiodic : Function.Periodic t (2 * Real.pi))
    (hmean : angularMean t = m)
    (hvar : angularMean (fun θ => (t θ - m) ^ 2) = ρ / a)
    (hspeed : v = a * (1 + m ^ 2) + ρ) : CircleDensity where
  rate θ := phaseDensity a v (t θ) / (2 * Real.pi)
  smooth := ((contDiff_const.mul (contDiff_const.add (ht.pow 2))).div_const v).div_const _
  positive θ := div_pos (phaseDensity_pos a v (t θ) ha hv) period_pos
  periodic := by intro θ; dsimp only; rw [hperiodic θ]
  integral_one := by
    rw [intervalIntegral.integral_div]
    exact (angular_rephasing_moments t a m ρ v (ne_of_gt ha) (ne_of_gt hv)
      ht.continuous hmean hvar hspeed).1

end
end NavierStokes.SmoothLoop
end
