public section

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

open OrderDual

/-- The order on `Prop` is a `CompleteLinearOrder`.

This is not an instance since `CompleteLinearOrder` includes decidability instances, which we want
to avoid for `Prop`. -/
@[expose, instance_reducible]
noncomputable def Prop.completeLinearOrder : CompleteLinearOrder Prop where
  __ := Prop.instCompleteLattice
  __ := Prop.linearOrder
  __ := BooleanAlgebra.toBiheytingAlgebra

end
