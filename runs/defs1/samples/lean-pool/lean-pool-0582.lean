@[expose] public section

namespace KaltonPeck.Support.GraphFredholm

noncomputable
section

open Coordinates Symplectic

open HilbertGlidingHump

open StrictlySingular

open Filter Function

open scoped ENNReal NNReal Topology lp BigOperators InnerProductSpace

universe uX uY

universe u

/-- The graph operator `R₀ + R₁T` on a presented model.
Support definition for blueprint labels `lem:even-odd-blocks` and `prop:graph-fredholm`. -/
def graphBlockOperator {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hX : RealKaltonPeckPresentation X) (T : X →L[ℝ] X) :
    X →L[ℝ] X := by
  exact evenBlockEmbedding hX + oddBlockEmbedding hX * T

end
end KaltonPeck.Support.GraphFredholm
end
