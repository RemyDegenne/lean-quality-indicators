@[expose] public section

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {D : Type u₃} [Bicategory.{w₃, v₃} D]

variable (B C)

namespace StrictlyUnitaryLaxFunctor

variable {B C}

section

attribute [local ext] StrictlyUnitaryLaxFunctor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma id_comp (F : StrictlyUnitaryLaxFunctor B C) :
    (StrictlyUnitaryLaxFunctor.id B).comp F = F := by
  ext
  · simp
  all_goals
  · rw [heq_iff_eq]
    ext
    simp

end
end StrictlyUnitaryLaxFunctor
end CategoryTheory
end
