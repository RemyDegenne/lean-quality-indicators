@[expose] public section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

namespace RightLift

variable {f : b ⟶ a} {g : c ⟶ a}

variable {s t : RightLift f g}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism between right lifts induced by a left unitor. -/
@[simps! hom_left inv_left]
def whiskerOfIdCompIsoSelf (t : RightLift f g) : (t.whisker (𝟙 c)).ofIdComp ≅ t :=
  CostructuredArrow.isoMk (λ_ (lift t))

end RightLift
end Bicategory
end CategoryTheory
end
