@[expose] public section

universe u v

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable (D : Subcoalgebra K C)

variable {D}

@[simp, norm_cast]
theorem coe_smul (r : K) (x : D) : ((r • x : D) : C) = r • (x : C) :=
  rfl

end Subcoalgebra
end
