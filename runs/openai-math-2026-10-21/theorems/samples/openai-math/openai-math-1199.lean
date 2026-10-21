namespace OAI

namespace LowSpaceSubsetSum

namespace CountedSort

variable {α : Type*}

theorem sort_steps_of_index_bits (cmp : α → α → Bool) (xs : List α) (n : ℕ)
    (hn : xs.length ≤ 2 ^ n) : (sort cmp xs).2 ≤ (6 * n + 1) * xs.length + 1 := by
  have hdepth : Nat.clog 2 xs.length ≤ n := Nat.clog_le_of_le_pow hn
  exact (sort_steps cmp xs).trans (by gcongr)

end CountedSort
end LowSpaceSubsetSum
end OAI
