@[expose] public section

universe u v

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

@[simp]
theorem mem_mk' (S : Submodule K C) (hS) (x : C) : x ∈ mk' S hS ↔ x ∈ S :=
  Iff.rfl

end Subcoalgebra
end
