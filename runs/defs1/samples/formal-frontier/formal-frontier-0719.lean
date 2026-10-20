@[expose] public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj

universe u v w

namespace AlgebraicGeometry

/-- The group-valued functor sending a `K`-algebra to its group of units. -/
def multiplicativeGroupFunctor
    (K : Type u) [CommRing K] : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of ((R : Type u)ˣ)
  map f := GrpCat.ofHom (Units.map f.hom)
  map_id R := by
    ext u
    rfl
  map_comp f g := by
    ext u
    rfl

end AlgebraicGeometry
end
end
