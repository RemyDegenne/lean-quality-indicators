public section

namespace CFSG.LocalAnalysis.GLTheoremA.BMType

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_factorial_of_bound {n N h K : ℕ} (hn : 25920 ≤ n) (hK : N < 25920 ^ (K + 1))
    (hKh : K.factorial < h) {k : ℕ} (hk : n ^ k ≤ N) : ¬ h ∣ k.factorial := by
  have hkK : k ≤ K := by
    by_contra hc
    push Not at hc
    have h1 : 25920 ^ (K + 1) ≤ 25920 ^ k := Nat.pow_le_pow_right (by norm_num) hc
    have h2 : 25920 ^ k ≤ n ^ k := Nat.pow_le_pow_left hn k
    omega
  intro hd
  have h1 : h ≤ k.factorial := Nat.le_of_dvd (Nat.factorial_pos k) hd
  have h2 : k.factorial ≤ K.factorial := Nat.factorial_le hkK
  omega

end CFSG.LocalAnalysis.GLTheoremA.BMType
end
