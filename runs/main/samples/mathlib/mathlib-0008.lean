public section

universe w w' v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {J : Type w} [Category.{w'} J]

lemma reflectsFiniteCoproducts_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.rightOp where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_rightOp
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

end CategoryTheory.Limits
end
