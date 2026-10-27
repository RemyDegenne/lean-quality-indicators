public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

theorem three_pow_mod_eight (a : ℕ) :
    (3 ^ a % 8 = 1 ∧ Even a) ∨ (3 ^ a % 8 = 3 ∧ Odd a) := by
  induction a with
  | zero => exact Or.inl ⟨by norm_num, ⟨0, rfl⟩⟩
  | succ a ih =>
    rw [pow_succ]
    rcases ih with ⟨h, he⟩ | ⟨h, ho⟩
    · exact Or.inr ⟨by omega, he.add_one⟩
    · exact Or.inl ⟨by omega, ho.add_one⟩

end CFSG.RankThree.PartTwo.Sec15.KS1424
end
