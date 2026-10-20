public section

open Matrix

open scoped MatrixGroups

variable {d : ℕ}

namespace Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R]

@[simp]
theorem disjoint_center_iff_neg_one_notMem [NoZeroDivisors R] [NeZero (2 : R)]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) R)) :
    Disjoint (Subgroup.center (SpecialLinearGroup (Fin 2) R)) Γ ↔
      (-1 : SpecialLinearGroup (Fin 2) R) ∉ Γ := by
  rw [← Subgroup.subgroupOf_eq_bot, ← Subgroup.card_eq_one]
  exact card_center_subgroupOf_eq_one_iff Γ

end Matrix.SpecialLinearGroup
end
