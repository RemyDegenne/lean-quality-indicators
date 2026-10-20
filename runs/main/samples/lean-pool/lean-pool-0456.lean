section

public section

noncomputable section

namespace EulerPacketInduction.Stage

open Set Finset Real InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerBaseDatum EulerPacketSupport EulerPacketSourceGeometry EulerPacketNormalizedPrimary
  EulerPacketInductionScales EulerPacketLowConstants EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketBaseGuardScales
  EulerParentRenewalScale EulerPacketGeometryLowBounds EulerParentNeighborThreshold
  EulerMeanHarmonic

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} {n : ℕ} (P : Stage S n)
  (hn : n ≠ 0) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

local notation "I" => P.joinedInput hn hq hB

local notation "G" => P.joinedGuards hn hq hB

local notation "k" => frequency S.J S.X n

local notation "hk" => S.normal_frequency n

local notation "ell" => supportScale S.J S.X (n+1)

local notation "F" => P.chooseJoined hn hq hB

theorem joinedState_eq :
    P.joinedState hn hq hB = GeometryJoinedChoice.state I P.restrictedState k hk ell
      (S.support_pos (n+1)) (S.support_one (n+1)) F symmetric := rfl

end EulerPacketInduction.Stage
end
end
end
