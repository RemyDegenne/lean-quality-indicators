@[expose] public section

universe w v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {J : Type u₂} [Category.{v₂} J]

attribute [local instance] hasLimitsOfShape_op_of_hasColimitsOfShape

/-- The colimit of `F.leftOp` is the unopposite of `limit F`. -/
def colimitLeftOpIsoUnopLimit (F : J ⥤ Cᵒᵖ) [HasLimit F] :
    colimit F.leftOp ≅ unop (limit F) :=
  colimit.isoColimitCocone ⟨_, isColimitCoconeLeftOpOfCone _ (limit.isLimit _)⟩

end CategoryTheory.Limits
end
end
