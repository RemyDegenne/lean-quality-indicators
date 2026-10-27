@[expose] public section

noncomputable section

universe w w' v u

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe uC' uC uD' uD

variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]

variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

attribute [instance 100] HasBinaryBiproducts.has_binary_biproduct

variable {P Q : C}

@[inherit_doc biprod]
notation:20 X " ⊞ " Y:20 => biprod X Y

/-- The inclusion into the first summand of a binary biproduct. -/
abbrev biprod.inl {X Y : C} [HasBinaryBiproduct X Y] : X ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inl

end CategoryTheory.Limits
end
end
