public section

universe w w' v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {J : Type w} [Category.{w'} J]

namespace Limits

/-- If `F.unop : C ⥤ D` creates finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite limits. -/
@[instance_reducible]
def createsFiniteLimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F.unop] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfUnop J F

end Limits
end CategoryTheory
end
end
