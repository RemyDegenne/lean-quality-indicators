@[expose] public section

noncomputable section

namespace EulerBaseDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerParentPacketFrames EulerBaseEulerGuards EulerTransverseFrameCoordinates

/-- Initial time, given by `guardTime solutionTime solutionLabelConstant`. -/
def initialTime : ℝ := guardTime solutionTime solutionLabelConstant

end EulerBaseDatum
end
end
