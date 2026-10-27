public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe u v

/-- The one-object homological complex associated to a square-zero endomorphism. -/
def oneObjectHomologicalComplex {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (X : C) (d : X ⟶ X) (d_comp_d : d ≫ d = 0) :
    HomologicalComplex C (ComplexShape.refl Unit) where
  X _ := X
  d _ _ := d
  d_comp_d' _ _ _ _ _ := d_comp_d

end TauCeti
end
