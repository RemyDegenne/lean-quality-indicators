@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter

open scoped ENNReal NNReal Topology

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- Continuous linear pairing against a fixed function in the conjugate Lᵖ space. -/
def lpPairingWith {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    (g : Lp ℝ q (volume : Measure Vec3)) :
    Lp ℝ p (volume : Measure Vec3) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ g).comp
    (ContinuousLinearMap.lpPairing volume p q (ContinuousLinearMap.mul ℝ ℝ))

end CKN.Foundation.Euclidean
end
end
