@[expose] public section

universe u v

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

@[simp]
theorem carrier_eq_coe (D : Subcoalgebra K C) : D.carrier = (D : Set C) :=
  rfl

end Subcoalgebra
end
