@[expose] public section

namespace CategoryTheory

namespace Functor

open scoped CategoryTheory.Prod

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C] {D : Type u₃}
  [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E] {H : Type u₅} [Category.{v₅} H]

variable (B C D E)

variable {B C D E}

lemma curry_obj_injective {F₁ F₂ : C × D ⥤ E} (h : curry.obj F₁ = curry.obj F₂) :
    F₁ = F₂ := by
  rw [← uncurry_obj_curry_obj F₁, ← uncurry_obj_curry_obj F₂, h]

end Functor
end CategoryTheory
end
