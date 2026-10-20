public section

open scoped BigOperators

namespace Fin

theorem finRotate_succ_succAbove_of_ne {n : ℕ} {i k : Fin n} (hk : k ≠ i) :
    finRotate (n + 1) (i.succ.succAbove k) = i.succ.succAbove (finRotate n k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  rw [Ne, Fin.ext_iff] at hk
  have := k.isLt
  have := i.isLt
  ext
  simp only [succAbove]
  split_ifs <;> simp only [lt_def, val_castSucc, val_succ, coe_finRotate, Fin.ext_iff,
    val_last] at * <;> split_ifs at * <;> omega

end Fin
end
