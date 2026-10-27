public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace

open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section Trace

variable {φ : C(E, ℝ)} {K : ℝ≥0}

/-- **The trace on the graph of a Lipschitz function.** For a `K`-Lipschitz `φ`, the trace of
`u ∈ H¹` of the region `{φ y < t}` above the graph is the
half-space trace of the flattened function `u ∘ (graphFlattening φ).symm`. It is an element of
`L²(E)`: the graph is parametrized by `y ↦ (φ y, y)`, the image under inverse flattening of the
boundary point `(0, y)` of the half-space. -/
def W1p.normalEpigraphTrace (hφ : LipschitzWith K φ) :
    W1p volume (normalEpigraph φ) 2 →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
  (W1p.halfSpaceTrace 0).comp (W1p.normalEpigraphEquivL hφ).toContinuousLinearMap

end Trace
end TauCeti
end
end
