@[expose] public section

noncomputable section

namespace EulerPacketPrimaryFactorization

open Set InnerProductSpace EulerSmoothLimit EulerTransversePacketProvider
  EulerPacketTerminalDatum EulerTransversePacketPrimary EulerSpatialCutoffs
  EulerLinearDuhamel EulerVolterraConvolution

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

theorem canonical_size_pos (hξ : ξ ≠ 0) (t : Icc (0 : ℝ) D.T) :
    0 < ‖D.normal.field t 0‖*‖canonicalVelocity τ hτ hτT B ξ hs t 0‖ :=
  mul_pos (norm_pos_iff.mpr (HistoryData.normal_ne_zero t 0))
    (norm_pos_iff.mpr (canonicalVelocity_center_ne_zero τ hτ hτT B ξ hs hξ t))

end EulerPacketPrimaryFactorization
end
end
