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

/-- The colimit of `F.unop` is the unopposite of `limit F`. -/
def colimitUnopIsoOpLimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] :
    colimit F.unop ≅ unop (limit F) :=
  colimit.isoColimitCocone ⟨_, isColimitCoconeUnopOfCone _ (limit.isLimit _)⟩

end CategoryTheory.Limits
end
end
