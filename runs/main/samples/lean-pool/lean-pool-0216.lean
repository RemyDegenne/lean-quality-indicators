section

section

@[expose] public section

noncomputable section

namespace EulerOrdinaryMollifier

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerNoncompactTransport EulerLpTranslation.SmoothL2Field

open scoped ContDiff Topology Convolution

theorem kernel_compact (n : ℕ) : HasCompactSupport (kernel n) := (bump n).hasCompactSupport_normed

end EulerOrdinaryMollifier
end
end
end
end
