public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v w w' u u'

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

variable {J : Type w} (f : Option J → C) [HasBiproduct f]
  [HasBiproduct fun j => f (some j)] [HasBinaryBiproduct (f none) (⨁ fun j => f (some j))]

@[simp]
theorem biprod_inl_biproductOptionIso_inv :
    biprod.inl ≫ (biproductOptionIso f).inv = biproduct.ι f none := by
  classical
  apply biproduct.hom_ext
  rintro (_ | j) <;> simp [biproductOptionIso]

end TauCeti
end
