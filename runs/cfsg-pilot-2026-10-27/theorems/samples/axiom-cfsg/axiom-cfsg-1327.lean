public section

namespace CFSG.ComponentClassification.GSThmB.P29

open DihedralGroup

section Center

variable {m : ℕ}

theorem two_pow_facts (hm : 2 ≤ m) : Even (2 ^ m) ∧ 2 ^ m ≠ 2 ∧ 2 ^ m / 2 = 2 ^ (m - 1) := by
  refine ⟨(Nat.even_pow' (by omega)).mpr even_two, ?_, ?_⟩
  · intro h
    have : 2 ^ m ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.add_sub_cancel]

end Center
end CFSG.ComponentClassification.GSThmB.P29
end
