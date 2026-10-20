public section

noncomputable section

open CategoryTheory TensorProduct

open scoped TensorProduct

universe u v w w₁ w₂

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (V : Type v) [AddCommGroup V] [Module K V]
  (R : Type w) [CommRing R] [Algebra K R]

/-- The general linear functor on the transported literal-order tensor module. -/
def sourceOrderedGeneralLinearFunctor : CommAlgCat.{w, u} K ⥤ GrpCat.{max w v} where
  obj R := GrpCat.of (LinearMap.GeneralLinearGroup R (SourceOrderedTensor K V R))
  map f := GrpCat.ofHom (sourceOrderedGeneralLinearBaseChange K V _ _ f.hom)
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro f
    exact sourceOrderedGeneralLinearBaseChange_id K V R f
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro h
    exact (sourceOrderedGeneralLinearBaseChange_comp K V _ _ _ f.hom g.hom h).symm

end AlgebraicGeometry
end
end
