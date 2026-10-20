@[expose] public section

noncomputable section

namespace EulerParentPacketFrames

open Set InnerProductSpace EulerSmoothLimit EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerAllOrderDriftCorrection EulerPacketPhysicalLowBounds

open scoped ContDiff

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

namespace GeometryJoinedChoice

variable (I : EulerPacketInitial.Input U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)

local notation "T" => (state I S k hk nextEll hnext hnext1 F hSym)

local notation "res" => (residual I S k hk nextEll hnext hnext1 F)

theorem increment_fderiv (t : Icc (0 : ℝ) I.parent.T) (x : Space) :
    fderiv ℝ (S.velocityIncrement T t) x =
      fderiv ℝ (I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates
        I.support I.support_compact F.Q res k S.evolution.inverse t) (I.parent.ell⁻¹ • x) := by
  have hnew := ((T).evolution.velocity_smooth t).differentiable (by simp) x
  have hold := (S.evolution.velocity_smooth t).differentiable (by simp) x
  change fderiv ℝ (fun y => (T).evolution.velocity (t,y)-S.evolution.velocity (t,y)) x = _
  rw [fderiv_fun_sub hnew hold, state_velocity I S k hk nextEll hnext hnext1 F hSym]
  have he := I.parent.exactPacketVelocity_fderiv I.normal I.normal_unit I.coordinates
    I.support I.support_compact F.Q res k S.evolution.inverse S.evolution.velocity t x hold
  rw [he,add_sub_cancel_left]

end GeometryJoinedChoice
end EulerParentPacketFrames
end
end
