@[expose] public section

noncomputable section

namespace EulerPacketSourceGeometry

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerPacketMovingFrame EulerPacketNormalizedPrimary
  EulerPacketCrossProduct EulerTransverseFrameCoordinates EulerPacketRay
  EulerPacketForwardFactorization

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U}

namespace ForwardGuards

variable {P : ParentFrame D 0} (G : ForwardGuards P)

variable [CompleteSpace U]

omit [CompleteSpace U] in
theorem sourceError_bound (x : Space) (hx : ‖x‖ ≤ G.radius)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) : ‖P.sourceError x t‖ ≤ P.forwardError G.radius := by
  have hd := EulerPacketActivationHistory.coefficient_difference D.M (D.clamp t) x 0
  have hr := P.remainder_bound t ht
  have he : P.sourceError x t = (sourceMatrix D x t-sourceMatrix D 0 t)+P.sourceError 0 t := by
    unfold ParentFrame.sourceError
    module
  rw [he]
  refine (norm_add_le _ _).trans ((add_le_add ((hd.trans_eq (by rw [sub_zero])).trans
    (mul_le_mul_of_nonneg_left hx (norm_nonneg _))) hr).trans_eq ?_)
  unfold ParentFrame.forwardError
  ring

end ForwardGuards
end EulerPacketSourceGeometry
end
end
