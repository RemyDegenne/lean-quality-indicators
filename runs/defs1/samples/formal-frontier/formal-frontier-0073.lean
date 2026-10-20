@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (D : Type u) [Fintype D]

/-- A genuine morphism of schemes over the base, induced by the coordinate map. -/
def additiveGroupAffineProductProjection (d : D) :
    additiveGroupAffineProductScheme K D ⟶ additiveGroupUnderlyingScheme K :=
  (algSpec (.of K)).map (CommAlgCat.ofHom (additiveProductCoordinateAlgHom K D d)).op

end AlgebraicGeometry
end
end
