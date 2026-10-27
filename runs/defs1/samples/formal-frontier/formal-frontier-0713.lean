public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CompletedGroupAlgebra

/-- The inverse system `U ↦ R[G/U]` over the open normal subgroups of a
profinite group `G`. -/
@[expose] def finiteQuotientSystem (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) :
    OpenNormalSubgroup G ⥤ RingCat.{max u v} :=
  ProfiniteGrp.diagram G ⋙
    forget₂ ProfiniteGrp GrpCat.{v} ⋙
    forget₂ GrpCat MonCat.{v} ⋙
    monoidAlgebraFunctor R

end CompletedGroupAlgebra
end
end
