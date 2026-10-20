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

theorem exists_normalizedRowRank_eq (k : ℕ) (hk : k ≤ Fintype.card n) :
    ∃ A : Matrix n n K,
      normalizedRowRank A = (k : ℝ) / Fintype.card n := by
  obtain ⟨A, hA⟩ := exists_rowRank_eq (K := K) k hk
  exact ⟨A, by rw [normalizedRowRank, hA]⟩

end Matrix
end
