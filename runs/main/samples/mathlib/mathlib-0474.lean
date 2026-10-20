@[expose] public section

open Nat

namespace Fin

variable {n : ℕ}

@[simp] lemma le_sub_one_iff {k : Fin (n + 1)} : k ≤ k - 1 ↔ k = 0 := by
  cases n
  · simp [fin_one_eq_zero k]
  rw [le_def, Nat.le_iff_lt_or_eq, val_fin_lt, lt_sub_iff, val_inj, eq_comm, sub_eq_self]
  simp

end Fin
end
