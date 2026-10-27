public section

namespace CFSG.ASVolI

open CFSG.Open

open CFSG.ASVolI.ChA

open scoped Pointwise MatrixGroups

theorem burnsideA315h_aut_three {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (6 * n)) {σ : RingAut F} (hσ : orderOf σ = 3) :
    ∃ e : ℕ, (e = 4 ^ n ∨ e = (4 ^ n) ^ 2) ∧ ∀ y : F, σ y = y ^ e := by
  obtain ⟨φ, hφ, hord, hzp, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 6 * n) hF
  have hfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  have hmem : σ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top σ
  rw [← hfin.mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  have h3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  rw [← hk, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hord] at h3
  have h2n : 2 * n ∣ k := by
    have h' : 3 * (2 * n) ∣ 3 * k := by
      have e1 : 6 * n = 3 * (2 * n) := by ring
      rw [e1] at h3
      rwa [mul_comm k 3] at h3
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h'
  obtain ⟨t, rfl⟩ := h2n
  have hS3 : (φ ^ (2 * n)) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * n * 3 = 6 * n by ring, ← hord]
    exact pow_orderOf_eq_one φ
  have hmod : ∀ m : ℕ, (φ ^ (2 * n)) ^ m = (φ ^ (2 * n)) ^ (m % 3) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hS3, one_pow, one_mul]
  have hσt : σ = (φ ^ (2 * n)) ^ (t % 3) := by
    rw [← hk, pow_mul, hmod]
  have ht3 : t % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hsq := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.pow_apply_of_sq hφ
  interval_cases h : t % 3
  · exfalso
    rw [pow_zero] at hσt
    rw [hσt, orderOf_one] at hσ
    omega
  · refine ⟨4 ^ n, Or.inl rfl, fun y => ?_⟩
    rw [hσt, pow_one, hsq (2 * n) y, pow_mul]
    norm_num
  · refine ⟨(4 ^ n) ^ 2, Or.inr rfl, fun y => ?_⟩
    rw [hσt, ← pow_mul, hsq (2 * n * 2) y]
    rw [pow_mul, pow_mul]
    norm_num

end CFSG.ASVolI
end
