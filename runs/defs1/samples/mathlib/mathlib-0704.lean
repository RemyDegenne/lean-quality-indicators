@[expose] public section

open CategoryTheory

variable (V : Type*) [Category* V] {FV : V → V → Type*} {CV : V → Type*}
    [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] [HasForget₂ V TopCat]

variable (G : Type*) [Monoid G] [TopologicalSpace G]

open Action

namespace ContAction

variable {V G}

variable (V) {H : Type*} [Monoid H] [TopologicalSpace H]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction of scalars along a topological monoid isomorphism induces an equivalence of
categories. -/
@[simps! functor inverse]
def resEquiv (f : G ≃ₜ* H) : ContAction V H ≌ ContAction V G where
  functor := res _ f
  inverse := res _ f.symm
  unitIso := resCongr V (ContinuousMonoidHom.id H) _ (by ext; simp) ≪≫
    ContAction.resComp _ _ _
  counitIso := (ContAction.resComp _ _ _).symm ≪≫
    ContAction.resCongr V _ (ContinuousMonoidHom.id G) (by ext; simp)

end ContAction
end
