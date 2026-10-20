public section

open Matrix

open scoped MatrixGroups

variable {d : ℕ}

namespace Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R]

@[simp]
theorem card_center_subgroupOf_eq_two_iff [NoZeroDivisors R] [NeZero (2 : R)]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) R)) :
    Nat.card ((Subgroup.center (SpecialLinearGroup (Fin 2) R)).subgroupOf Γ) = 2 ↔
      (-1 : SpecialLinearGroup (Fin 2) R) ∈ Γ := by
  obtain ⟨hpos, hle⟩ := card_center_subgroupOf_pos_and_le_two Γ
  constructor
  · intro h
    by_contra hneg
    have h1 := (card_center_subgroupOf_eq_one_iff Γ).mpr hneg
    omega
  · intro hneg
    have h1 : Nat.card ((Subgroup.center (SpecialLinearGroup (Fin 2) R)).subgroupOf Γ) ≠ 1 :=
      fun h ↦ (card_center_subgroupOf_eq_one_iff Γ).mp h hneg
    omega

end Matrix.SpecialLinearGroup
end
