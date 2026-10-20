@[expose] public section

universe w v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {J : Type u₂} [Category.{v₂} J]

/-- Turn a limit for `F.rightOp : J ⥤ Cᵒᵖ` into a colimit for `F : Jᵒᵖ ⥤ C`. -/
@[simps]
def isColimitCoconeOfConeRightOp (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp} (hc : IsLimit c) :
    IsColimit (coconeOfConeRightOp c) where
  desc s := (hc.lift (coneRightOpOfCocone s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsLimit.fac] using! w (op j)

end CategoryTheory.Limits
end
end
