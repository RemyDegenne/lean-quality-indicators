public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

open CFSG.LocalAnalysis.GLTheoremA.S10

namespace CatDistinct

theorem orderA_one_two_pow {k : ℕ} (hk : 1 ≤ k) :
    ∃ O, Odd O ∧ O % 4 = 3 ∧ orderA 1 (2 ^ k) = 2 ^ k * O := by
  have hg : Nat.gcd (1 + 1) (2 ^ k - 1) = 1 := by
    have : Odd (2 ^ k - 1) := odd_two_pow_sub_one hk
    exact Nat.coprime_two_left.2 this
  refine ⟨(2 ^ k) ^ 2 - 1, odd_pow_two_pow_sub_one hk (by norm_num), ?_, ?_⟩
  · have h2 := four_dvd_pow_two_mul hk (by norm_num : 2 ≤ 2)
    have p2 : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  · simp [orderA, hg]

end CatDistinct
end CFSG.LocalAnalysis.GLTheoremA
end
