@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.GeometryForwardChoice

open Set InnerProductSpace EulerSmoothLimit EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketGeometryLowBounds EulerMeanHarmonic

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : GeometryForwardInput U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)

/-- Low bounds as an element of `LowBounds F.parent`. -/
def lowBounds (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K + 2 * CM * I.geometry.hchild * (I.geometry.δ * goodRatio +
        I.geometry.earlyRatio) + k ^ (-(1 / 4 : ℝ))) * (I.parent.T ^ 2 / 2) + (I.low.Be +
        (I.geometry.hchild * I.geometry.earlyRatio + k ^ (-(1 / 4 : ℝ)))) * I.parent.T +
        boundaryLocalizationC2 * (I.low.Bc + (I.geometry.hchild * I.geometry.earlyRatio +
        k ^ (-(1 / 4 : ℝ)))) * I.low.r ^ 3 * I.parent.T ≤ 1 / 2) : LowBounds F.parent := by
  let res := forwardInitializedApproximationResidual I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement (truncation k) F.hn k hk.four
  let V := forwardInitializedNormalizedField I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha (truncation k) k
  exact S.evolution.forwardChildLowBounds I.normal I.normal_unit I.coordinates I.support
      I.support_compact
    F.Q res V rfl F.flow F.coefficient k (mul_inv_cancel₀ hk.pos.ne') F.graph nextEll hnext hnext1
    I.geometry I.halfBall I.delta_pos I.delta_le_one I.low
    (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH F.errors hCM hCH hsmall

end EulerParentPacketFrames.GeometryForwardChoice
end
end
