public section

namespace TauCeti

namespace PlumbingCube

variable {V : Type*} [DecidableEq V]

variable [DecidableEq (V → ℤ)]

/-- The vertices of a bundled plumbing cube. -/
noncomputable irreducible_def vertices (C : PlumbingCube V) : Finset (V → ℤ) :=
  PlumbingGraph.cubeVertices C.base C.directions

end PlumbingCube
end TauCeti
end
