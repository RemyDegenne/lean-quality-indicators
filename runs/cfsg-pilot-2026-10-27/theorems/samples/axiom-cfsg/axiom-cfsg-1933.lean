public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)

open scoped MatrixGroups Pointwise commutatorElement

namespace Lemma113Claims

variable {G : Type} [Group G] [Finite G]

section Lift

section IndexClaim

theorem commute_of_odd_pow_mem_normalizer {n y : G}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G)) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    {m : ℕ} (hm : Odd m) (hnm : n ^ m = 1) : Commute n y := by
  obtain ⟨k, hk, hnk⟩ := Lemma113d.conj_eq_zpow_of_mem_normalizer hn hy3 hy1
  have hpow : ∀ j : ℕ, n ^ j * y * (n ^ j)⁻¹ = y ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : n ^ (j + 1) * y * (n ^ (j + 1))⁻¹ = n * (n ^ j * y * (n ^ j)⁻¹) * n⁻¹ := by
        rw [pow_succ']
        group
      rw [h1, ih]
      have h2 : n * y ^ (k ^ j) * n⁻¹ = (n * y * n⁻¹) ^ (k ^ j) := conj_zpow.symm
      rw [h2, hnk, ← zpow_mul, pow_succ, mul_comm (k ^ j) k]
  have hfix : y ^ (k ^ m) = y := by
    rw [← hpow, hnm]
    group
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hdvd : (orderOf y : ℤ) ∣ k ^ m - 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.2
    rw [zpow_sub, zpow_one, hfix, mul_inv_cancel]
  rw [hord] at hdvd
  have hz : ((k ^ m - 1 : ℤ) : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hdvd
  have hk0 : (k : ZMod 3) ≠ 0 := by
    intro h0
    exact hk ((ZMod.intCast_zmod_eq_zero_iff_dvd k 3).1 h0)
  rw [Int.cast_sub, Int.cast_one, sub_eq_zero, Int.cast_pow, zmod3_pow_odd _ hk0 hm] at hz
  have hk1 : ((3 : ℕ) : ℤ) ∣ k - 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 3).1 (by rw [Int.cast_sub, Int.cast_one, hz, sub_self])
  rw [← hord] at hk1
  have hek : y ^ k = y := by
    have h1 : y ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 hk1
    calc y ^ k = y ^ (k - 1 + 1) := by rw [sub_add_cancel]
      _ = y ^ (k - 1) * y := zpow_add_one y (k - 1)
      _ = y := by rw [h1, one_mul]
  have hcomm : n * y * n⁻¹ = y := by rw [hnk, hek]
  show n * y = y * n
  calc n * y = (n * y * n⁻¹) * n := by group
    _ = y * n := by rw [hcomm]

end IndexClaim
end Lift
end Lemma113Claims
end CFSG.LocalAnalysis.GLTheoremB.MovingAround
end
