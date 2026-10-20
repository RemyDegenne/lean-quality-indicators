set_option warningAsError true

@[expose] public section

open Function

open scoped Kronecker

universe u v w x y

namespace Matrix

variable {K : Type u} [DivisionRing K]

variable {m : Type v} {n : Type w} {p : Type x}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

section PositiveSize

variable [Nonempty n]

theorem normalizedRowRank_mem_Icc (A : Matrix n n K) :
    normalizedRowRank A ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) card_cast_pos.le
  · have hcast : (rowRank A : ℝ) ≤ (Fintype.card n : ℝ) := by
      exact_mod_cast rowRank_le_card A
    calc
      normalizedRowRank A ≤ (Fintype.card n : ℝ) / Fintype.card n :=
        (div_le_div_iff_of_pos_right card_cast_pos).2 hcast
      _ = 1 := div_self card_cast_pos.ne'

end PositiveSize
end Matrix
end
