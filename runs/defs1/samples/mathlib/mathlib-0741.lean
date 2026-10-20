@[expose] public section

open Finset Set

variable (𝕜 E : Type*) [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace Geometry

namespace SimplicialComplex

variable {𝕜 E}

variable {K : SimplicialComplex 𝕜 E} {s t : Finset E} {x : E}

/-- The vertices of a simplicial complex are its zero-dimensional faces. -/
def vertices (K : SimplicialComplex 𝕜 E) : Set E :=
  { x | {x} ∈ K.faces }

end SimplicialComplex
end Geometry
end
