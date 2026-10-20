public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- The group-valued functor sending a `K`-algebra to its additive group.
`Multiplicative` changes only the operation tag required by `GrpCat`. -/
@[expose] def additiveGroupFunctor
    (K : Type u) [CommRing K] : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Multiplicative R)
  map f := GrpCat.ofHom (AddMonoidHom.toMultiplicative f.hom.toAddMonoidHom)
  map_id _ := by
    apply GrpCat.hom_ext
    rfl
  map_comp _ _ := by
    apply GrpCat.hom_ext
    rfl

end AlgebraicGeometry
end
end
