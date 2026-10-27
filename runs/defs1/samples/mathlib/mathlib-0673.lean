@[expose] public section

universe w w' w'' v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

variable [LocallySmall.{w} C]

section Coyoneda

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `shrinkCoyoneda` is compatible with `uliftFunctor`. -/
noncomputable
def shrinkCoyonedaUliftFunctorIso [LocallySmall.{max w w'} C] :
    shrinkCoyoneda.{w} ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{w', w} ≅
      shrinkCoyoneda :=
  NatIso.ofComponents
    (fun X ↦ FunctorToTypes.shrinkCompUliftFunctorIso.{w, v} (coyoneda.obj X))
    fun _ ↦ by ext; simp [shrinkYoneda]

end Coyoneda
end CategoryTheory
end
