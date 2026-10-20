@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric

open scoped ENNReal NNReal Topology

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The spatial pressure residual at a fixed time for a compactly supported test. -/
def pressureSliceResidual {Ω : Set Vec3} {u : ParabolicPoint → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (ψ : Vec3 → ℝ) (s : ℝ) : ℝ :=
  (∫ x in Ω, p (x, s) * spatialLaplacian ψ x) +
    (∫ x in Ω, ∑ i, ∑ j, u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
    ∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv ψ i x

end CKN
end
end
