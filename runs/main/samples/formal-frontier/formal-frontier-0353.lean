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

theorem normalizedRowRank_mul_le_left (A B : Matrix n n K) :
    normalizedRowRank (A * B) ≤ normalizedRowRank A := by
  exact (div_le_div_iff_of_pos_right card_cast_pos).2
    (by exact_mod_cast rowRank_mul_le_left A B)

end PositiveSize
end Matrix
end
