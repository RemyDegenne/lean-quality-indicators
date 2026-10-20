@[expose] public section

open scoped symmDiff

variable {α β γ : Type*}

scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.sup

scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.inf

scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.toBooleanAlgebra

section AlgebraToRing

variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ]

scoped[BooleanRingOfBooleanAlgebra]
  attribute [instance] GeneralizedBooleanAlgebra.toNonUnitalCommRing BooleanAlgebra.toBooleanRing

@[simp]
theorem ofBoolRing_add (a b : AsBoolRing α) : ofBoolRing (a + b) = ofBoolRing a ∆ ofBoolRing b :=
  rfl

end AlgebraToRing
end
