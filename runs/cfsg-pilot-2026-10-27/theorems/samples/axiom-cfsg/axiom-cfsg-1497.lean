public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

namespace Proof1721

section Frame

variable {E : Type} [Group E]

theorem conj_eq_of_mem_zpowers {M : Type} [Group M] {c k : M} (hc3 : orderOf c = 3)
    (hk : k * c * k⁻¹ ∈ Subgroup.zpowers c) (hkc : k * c * k⁻¹ ≠ c⁻¹) : k * c * k⁻¹ = c := by
  have hc : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hk
  rw [zpow_emod_three hc] at hn
  obtain h | h | h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  · exfalso
    rw [h, zpow_zero] at hn
    have h1 : k * c * k⁻¹ = 1 := hn.symm
    rw [mul_inv_eq_one, mul_eq_left] at h1
    rw [h1, orderOf_one] at hc3
    omega
  · rw [h, zpow_one] at hn
    exact hn.symm
  · exfalso
    apply hkc
    rw [← hn, h, eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num]
    exact_mod_cast hc

end Frame
end Proof1721
end CFSG.RankThree.PartTwo.Sec17
end
