public section

universe w w' v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {J : Type w} [Category.{w'} J]

lemma reflectsColimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.op F] :
    ReflectsColimit K F.unop where
  reflects {_} hc := ⟨isColimitOfOp (isLimitOfReflects F hc.op)⟩

end CategoryTheory.Limits
end
