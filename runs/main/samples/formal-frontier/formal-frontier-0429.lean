@[expose] public section

universe u v

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

@[simp]
theorem coe_mk' (S : Submodule K C) (hS) : (mk' S hS : Set C) = S :=
  rfl

end Subcoalgebra
end
