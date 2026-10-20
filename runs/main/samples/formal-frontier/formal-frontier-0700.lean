@[expose] public section

universe u v

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable (D : Subcoalgebra K C)

variable {D}

theorem coe_mem (x : D) : (x : C) ∈ D :=
  x.property

end Subcoalgebra
end
