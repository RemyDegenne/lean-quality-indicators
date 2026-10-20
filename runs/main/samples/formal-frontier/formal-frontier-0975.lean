@[expose] public section

universe u v

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

@[simp]
theorem coe_toSubmodule (D : Subcoalgebra K C) : (D.toSubmodule : Set C) = D :=
  rfl

end Subcoalgebra
end
