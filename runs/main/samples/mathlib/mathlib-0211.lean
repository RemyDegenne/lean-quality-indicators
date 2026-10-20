@[expose] public section

variable {R E F G : Type*}

local notation3 "R≥0" => Nonneg R

namespace PointedCone

open Function Submodule

open scoped Pointwise

notation:70 R:70 " ∙₊ " x:70 => hull R (singleton x)

section Lineal

variable [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup E] [Module R E]

theorem lineal_eq_sSup (C : PointedCone R E) : C.lineal = sSup {S : Submodule R E | S ≤ C} := by
  simp_rw [gc_ofSubmodule_lineal.le_iff_le, Set.Iic_def, csSup_Iic]

end Lineal
end PointedCone
end
