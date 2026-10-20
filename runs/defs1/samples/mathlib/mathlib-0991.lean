@[expose] public section

namespace CategoryTheory

open Bicategory.Opposite Opposite Pseudofunctor StrongTrans

universe w v u

namespace Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing of `1`-morphisms seen as a functor from `a ⟶ b` to the hom-category of the
corresponding pseudofunctors.

This is an implementation detail, and `Bicategory.yoneda.map` should be preferred. -/
@[simps!]
def postcomposing₂ (a b : B) : (a ⟶ b) ⥤ (yoneda₀ a ⟶ yoneda₀ b) where
  obj := postcomp₂
  map η := { as := { app x := (postcomposingCat (unop x) a b).map η } }

end Bicategory
end CategoryTheory
end
