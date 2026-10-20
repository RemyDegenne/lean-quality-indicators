@[expose] public section

universe u v

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable (D : Subcoalgebra K C)

theorem smul_mem (r : K) {x : C} (hx : x ∈ D) : r • x ∈ D :=
  D.toSubmodule.smul_mem r hx

end Subcoalgebra
end
