@[expose] public section

namespace VirasoroProject

section

open Module

variable (𝕜 : Type*) [CommRing 𝕜]

variable (𝓰 : Type*) [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]

namespace TriangularDecomposition

variable {𝕜 𝓰}

variable (tri : TriangularDecomposition 𝕜 𝓰)

/-- The positive part of a triangular decomposition. -/
abbrev upper := tri.part 1

end TriangularDecomposition
end
end VirasoroProject
end
