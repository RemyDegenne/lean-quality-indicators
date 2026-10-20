public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C} {P : ObjectProperty C}

namespace FiniteResolution

section Map

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  {E' : ExactStructure D} {P' : ObjectProperty D} {F : C ⥤ D} [F.Additive]
  (hF : E.IsConflationExact E' F) (hPP' : P ≤ P'.inverseImage F)

/-- The terms of the image of a resolution under a conflation-exact functor `F` are the images of
its terms: the identity in degrees up to the length, and the isomorphism `0 ≅ F 0` beyond it. -/
noncomputable def termMapIso : ∀ {X : C} (r : FiniteResolution E P X) (n : ℕ),
    (r.map hF hPP').term n ≅ F.obj (r.term n)
  | X, .base _, 0 => Iso.refl (F.obj X)
  | _, .base _, _ + 1 => F.mapZeroObject.symm
  | _, .step (Q := Q) _ _ _ _ _ _, 0 => Iso.refl (F.obj Q)
  | _, .step _ _ _ _ _ r, n + 1 => termMapIso r n

end Map
end FiniteResolution
end ExactStructure
end TauCeti
end
