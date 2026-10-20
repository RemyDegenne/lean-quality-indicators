@[expose] public section

noncomputable section

namespace EulerPacketInductionScales.Scales

open Real Finset EulerScale EulerBaseDatum EulerPacketLowConstants
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketSourceScaleActual EulerPacketSourceScaleGuards
  EulerPacketBaseGuardScales EulerPacketPressureScale EulerParentRenewalScale
  EulerPacketUniformSource EulerPacketSourceFrequency

variable {c B : ℝ} (S : Scales c B)

theorem support_pos (n : ℕ) : 0 < supportScale S.J S.X n := exp_pos _

end EulerPacketInductionScales.Scales
end
end
