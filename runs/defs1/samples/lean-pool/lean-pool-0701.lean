section

@[expose] public section

namespace NavierStokes.TrueConeLoop

noncomputable section

open Set Filter MeasureTheory

open SmoothLoop LoopMoments LoopVariance ConeAlgebra

open scoped ContDiff Topology Interval

/-- Variance root, given by `correctionRoot δ v / Real.sqrt a`. -/
def varianceRoot (a δ v : ℝ) : ℝ := correctionRoot δ v / Real.sqrt a

end
end NavierStokes.TrueConeLoop
end
end
