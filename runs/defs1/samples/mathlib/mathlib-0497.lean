@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

open CategoryTheory

variable {J : Type u₁} [Category.{v₁} J]

variable {K : Type u₂} [Category.{v₂} K]

variable {C : Type u₃} [Category.{v₃} C]

variable {D : Type u₄} [Category.{v₄} D]

variable {E : Type u₅} [Category.{v₅} E]

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory

namespace Limits

section

variable {F : Jᵒᵖ ⥤ Cᵒᵖ}

/-- Change a cone on `F : Jᵒᵖ ⥤ Cᵒᵖ` into a cocone on `F.unop : J ⥤ C`. -/
@[to_dual (attr := implicit_reducible, simps)
/-- Change a cocone on `F : Jᵒᵖ ⥤ Cᵒᵖ` into a cone on `F.unop : J ⥤ C`. -/]
def coconeUnopOfCone (c : Cone F) : Cocone F.unop where
  pt := unop c.pt
  ι := NatTrans.unop c.π

end
end Limits
end CategoryTheory
end
