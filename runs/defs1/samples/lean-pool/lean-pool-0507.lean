@[expose] public section

noncomputable section

namespace EulerMeanVectorIdentities

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanCutoffCurl EulerMeanGradientTest EulerMeanHarmonic

open scoped ContDiff

/-- Laplacian test, given by `⟨Δ (f : Space → Space), vector_laplacian_smooth f f.smooth,
vector_laplacian_compact f f.smooth f.compact⟩`. -/
def laplacianTest (f : Test) : Test :=
  ⟨Δ (f : Space → Space), vector_laplacian_smooth f f.smooth,
    vector_laplacian_compact f f.smooth f.compact⟩

end EulerMeanVectorIdentities
end
end
