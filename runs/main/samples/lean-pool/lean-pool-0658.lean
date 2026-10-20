@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPhysicalL2Scaling
  EulerAllOrderDriftCorrection EulerPacketCoordinates

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

include hTime in
theorem forwardInitializedInitialHigh_support
    (hS : D.support ⊆ Metric.closedBall 0 (1 / 2 : ℝ)) (N : ℕ) (k : ℝ) :
    tsupport (forwardInitializedInitialHigh M D δ hδ ξ hs α N k) ⊆
      Metric.closedBall 0 (M.ℓ/2) := by
  have h := EulerPacketInitial.high_scaled_support
    (fun i (_ : i ≤ N) => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i)
    ⟨0,le_rfl,M.T_pos.le⟩ k⁻¹ k D.m₀ M.ℓ M.ℓ_pos (1/2) hS
  simpa only [forwardInitializedInitialHigh,div_eq_mul_inv,one_mul] using h

end EulerPacketTerminalDatum
end
end
