@[expose] public section

noncomputable section

universe w w' v u

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe uC' uC uD' uD

variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]

variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

namespace BinaryBicone

variable {P P' Q Q' : C}

set_option backward.defeqAttrib.useBackward true in
/-- A binary bicone is a limit cone if and only if the corresponding bicone is a limit cone. -/
def toBiconeIsLimit {X Y : C} (b : BinaryBicone X Y) :
    IsLimit b.toBicone.toCone ≃ IsLimit b.toCone :=
  IsLimit.equivIsoLimit <| Cone.ext (Iso.refl _) fun ⟨as⟩ => by cases as <;> simp

end BinaryBicone
end CategoryTheory.Limits
end
end
