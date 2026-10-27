public section

noncomputable section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

/-- The carrier of the geometric realization (polyhedron) of an abstract simplicial complex. -/
noncomputable abbrev Realization (K : AbstractSimplicialComplex ι) : Type _ :=
  (standardGeometricComplex K).space

end AbstractSimplicialComplex
end
end
