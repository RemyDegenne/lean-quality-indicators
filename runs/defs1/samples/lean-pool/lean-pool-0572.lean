section

section

@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanBoundary
  EulerMeanCurlTensor

/-- Boundary localization C2, given by `4 * weakHarmonicSmallBallConstant`. -/
def boundaryLocalizationC2 : ℝ := 4 * weakHarmonicSmallBallConstant

end EulerMeanHarmonic
end
end
end
end
