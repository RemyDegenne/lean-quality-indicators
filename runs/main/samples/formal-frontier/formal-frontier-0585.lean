@[expose] public section

universe u v

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

@[simp]
theorem mem_top {x : C} : x ∈ (⊤ : Subcoalgebra K C) :=
  Submodule.mem_top

end Subcoalgebra
end
