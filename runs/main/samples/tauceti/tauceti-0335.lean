public section

namespace TauCeti

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

section HasShift

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]

variable {C D A}

@[simp]
lemma shiftFunctorAdd_prod_hom_app_snd (a b : A) (X : C × D) :
    ((shiftFunctorAdd (C × D) a b).hom.app X).2 = (shiftFunctorAdd D a b).hom.app X.2 :=
  rfl

end HasShift
end TauCeti
end
