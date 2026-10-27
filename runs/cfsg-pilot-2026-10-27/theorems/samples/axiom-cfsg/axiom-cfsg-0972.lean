public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup CFSG.Open

open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars statedProjCongr)

section

set_option linter.unusedSectionVars false

theorem three_dvd_two_pow_sq_sub_one (f : ℕ) : 3 ∣ (2 ^ f) ^ 2 - 1 := by
  have h : (2 ^ f) ^ 2 = 4 ^ f := by
    rw [sq, ← mul_pow]
    norm_num
  rw [h]
  have h1 : (1 : ℕ) ≡ 4 [MOD 3] := rfl
  have h2 := h1.pow f
  rw [one_pow] at h2
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 h2

end
end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
end
