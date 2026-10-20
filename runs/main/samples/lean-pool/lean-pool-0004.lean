section

@[expose] public section

noncomputable section

namespace EulerPacketPrimaryShear

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerGraphPullback EulerPacketNormalizedPrimary
  EulerTransversePacketProvider EulerPacketTerminalDatum EulerTransversePacketPrimary
  EulerSpatialCutoffs EulerPeriodicProfile EulerPacketPrimaryFactorization

open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

theorem fullWave_physical_canonical_norm (α k : ℝ) (hα : 0 ≤ α) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y) :
    ‖fderiv ℝ (fun x => fullWave τ hτ hτT B δ hδ ξ hs α k t (Y x)) (X 0)‖ =
      (α/δ) * (‖D.normal.field t 0‖ * ‖canonicalVelocity τ hτ hτT B ξ hs t 0‖) := by
  rw [fullWave_physical_norm τ hτ hτT B δ hδ ξ hs α k hα hk t X Y hX hY hleft,
    envelopedVelocity_independent_profile τ hτ hτT B δ 1 hδ zero_lt_one]
  rfl

end EulerPacketPrimaryShear
end
end
end
