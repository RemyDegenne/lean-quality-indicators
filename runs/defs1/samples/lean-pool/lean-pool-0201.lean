@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

noncomputable section

namespace CKN.Foundation.Parabolic

/-- Uncentered Hardy–Littlewood maximal function over parabolic balls. -/
def parabolicMaximalFunction (f : ParabolicPoint → ℝ≥0∞) (z : ParabolicPoint) : ℝ≥0∞ :=
  ⨆ c : ParabolicPoint, ⨆ r : ℝ,
    (hardyLittlewoodParabolicMetricBall c r).indicator
      (fun _ ↦ ⨍⁻ y in hardyLittlewoodParabolicMetricBall c r, f y ∂volume) z

end CKN.Foundation.Parabolic
end
end
