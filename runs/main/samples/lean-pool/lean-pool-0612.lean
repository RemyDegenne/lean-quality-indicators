@[expose] public section

namespace LeanPool.PoincareThreeBody

open MeasureTheory Set

open scoped Interval

lemma resonantCombinedCorrection_periodic
    (F : ℝ → PhaseSpace → ℝ) {p q : ℕ} (hp : 0 < p)
    {eccentricity orientation : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) :
    resonantCombinedCorrection F p q eccentricity orientation (resonantOrbitPeriod p) =
      resonantCombinedCorrection F p q eccentricity orientation 0 := by
  unfold resonantCombinedCorrection
  rw [show resonantOrbitPeriod p = 0 + resonantOrbitPeriod p by ring,
    resonantDisturbingFunction_add_period hp heccentricity heccentricityOne]
  simp only [zero_add]
  rw [resonantCandidateCorrection_periodic F hp heccentricity heccentricityOne]

end LeanPool.PoincareThreeBody
end
