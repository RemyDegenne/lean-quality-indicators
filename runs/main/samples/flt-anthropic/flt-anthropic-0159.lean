namespace P2MW.S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open Polynomial

namespace AXL

variable (p : ℕ) [hp : Fact p.Prime]

local notation "Ω" => PadicAlgCl p

local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

theorem main (n : ℕ) : ∀ (K : IntermediateField ℚ_[p] Ω) (α : Ω) (δ : ℝ),
    (minpoly K α).natDegree ≤ n →
    (∀ σ : Γ, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) →
      ∃ a ∈ K, ‖α - a‖ ≤ B p n * δ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K α δ hdeg hconj
    have hδ : 0 ≤ δ := by
      have := hconj 1 (Subgroup.one_mem _)
      simpa using this
    have hint := isIntegralK p K α
    set n₀ := (minpoly K α).natDegree with hn₀
    have hn₀pos : 0 < n₀ := minpoly.natDegree_pos hint

    by_cases h1 : n₀ = 1
    · have hα : α ∈ (algebraMap K Ω).range := minpoly.natDegree_eq_one_iff.mp h1
      obtain ⟨a, ha⟩ := hα
      refine ⟨(a : Ω), a.2, ?_⟩
      have : (a : Ω) = α := ha
      rw [this, sub_self, norm_zero]
      exact mul_nonneg (B_pos p n).le hδ
    have hn₀2 : 2 ≤ n₀ := by omega

    set L := Nat.log p n₀ with hL
    have hpL : p ^ L ≤ n₀ := Nat.pow_log_le_self p (by omega)
    have hn₀lt : n₀ < p ^ (L + 1) := Nat.lt_pow_succ_log_self hp.out.one_lt n₀

    set f : (Polynomial (PadicAlgCl p)) := (minpoly K α).map (algebraMap K Ω) with hf
    have hfmon : f.Monic := (minpoly.monic hint).map _
    have hfdeg : f.natDegree = n₀ := (minpoly.monic hint).natDegree_map _
    have hroots : ∀ β ∈ f.roots, ‖β - α‖ ≤ δ := roots_minpoly_norm_sub_le p K α δ hconj

    have cont : ∀ (m : ℕ) (Λ : ℝ), 0 < m → m < n₀ → 1 ≤ Λ →
        (n₀.choose (n₀ - m) : Ω) ≠ 0 →
        (‖(n₀.choose (n₀ - m) : Ω)‖)⁻¹ ≤ Λ ^ m →
        B p m * Λ ≤ B p n₀ →
        ∃ a ∈ K, ‖α - a‖ ≤ B p n * δ := by
      intro m Λ hm0 hmn hΛ1 hN hNΛ hBΛ
      set j := n₀ - m with hj
      have hjlt : j < f.natDegree := by rw [hfdeg]; omega
      have hmj : f.natDegree - j = m := by rw [hfdeg]; omega
      have hNf : (f.natDegree.choose j : Ω) ≠ 0 := by rw [hfdeg]; exact hN
      obtain ⟨β, hβ, hβle⟩ := key p f hfmon α δ hδ hroots j hjlt hNf
      rw [hmj, hfdeg] at hβle

      have hβΛ : ‖β - α‖ ≤ Λ * δ := by
        have hΛδ : 0 ≤ Λ * δ := mul_nonneg (zero_le_one.trans hΛ1) hδ
        refine le_of_pow_le_pow_left₀ hm0.ne' hΛδ ?_
        refine hβle.trans ?_
        rw [div_eq_mul_inv, mul_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right hNΛ (pow_nonneg hδ m)

      have hβdeg : (minpoly K β).natDegree ≤ m := by
        have := natDegree_minpoly_le_of_mem_roots_hasseDeriv p K α j (by omega) β
          (by rw [← hf]; exact hβ)
        omega

      have hβconj := norm_conj_sub_le p K α β δ (Λ * δ) hconj hβΛ
        (by nlinarith [hδ, hΛ1])

      have hmn' : m < n := lt_of_lt_of_le hmn hdeg
      obtain ⟨a, haK, ha⟩ := ih m hmn' K β (Λ * δ) hβdeg hβconj
      refine ⟨a, haK, ?_⟩
      have hsplit : α - a = (α - β) + (β - a) := by abel
      rw [hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_sub_rev]
        refine hβΛ.trans ?_
        have : Λ ≤ B p n := by
          have h1 : Λ ≤ B p m * Λ := le_mul_of_one_le_left (zero_le_one.trans hΛ1) (one_le_B p m)
          exact h1.trans (hBΛ.trans (B_mono p hdeg))
        exact mul_le_mul_of_nonneg_right this hδ
      · refine ha.trans ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hBΛ.trans (B_mono p hdeg)) hδ
    by_cases hcase : p ^ L < n₀
    ·
      refine cont (p ^ L) 1 (pow_pos hp.out.pos L) hcase le_rfl ?_ ?_ ?_
      · rw [Nat.choose_symm hpL]
        have h := not_dvd_choose_prime_pow p hpL hn₀lt
        intro h0
        have h1 : ‖((n₀.choose (p ^ L) : ℕ) : Ω)‖ = 1 := norm_natCast_eq_one p h
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      · rw [Nat.choose_symm hpL, norm_natCast_eq_one p (not_dvd_choose_prime_pow p hpL hn₀lt),
          inv_one, one_pow]
      · rw [mul_one]; exact B_mono p hpL
    ·
      have hn₀eq : n₀ = p ^ L := le_antisymm (not_lt.mp hcase) hpL
      have hL1 : 1 ≤ L := by
        by_contra hL0
        push Not at hL0
        have : L = 0 := by omega
        rw [this, pow_zero] at hn₀eq
        omega
      set m := p ^ (L - 1) with hm
      have hm0 : 0 < m := pow_pos hp.out.pos _
      have hmn : m < n₀ := by
        rw [hn₀eq, hm]
        exact Nat.pow_lt_pow_right hp.out.one_lt (by omega)
      have hmle : m ≤ n₀ := hmn.le
      have hNnat : ¬ p ^ 2 ∣ n₀.choose m := by
        rw [hn₀eq, hm]; exact not_sq_dvd_choose_prime_pow_pred p hL1
      have hNne : n₀.choose m ≠ 0 := (Nat.choose_pos hmle).ne'
      set Λ : ℝ := (p : ℝ) ^ ((m : ℝ)⁻¹) with hΛ
      have hΛ1 : 1 ≤ Λ := Real.one_le_rpow (one_le_p p) (by positivity)
      refine cont m Λ hm0 hmn hΛ1 ?_ ?_ ?_
      · rw [Nat.choose_symm hmle]
        exact_mod_cast hNne
      · rw [Nat.choose_symm hmle]
        have hle := inv_p_le_norm_natCast p hNne hNnat
        have hΛm : Λ ^ m = p := by
          rw [hΛ]; exact Real.rpow_inv_natCast_pow (p_pos p).le hm0.ne'
        rw [hΛm]
        rw [inv_le_comm₀ (norm_natCast_pos p hNne) (p_pos p)]
        exact hle
      ·
        have hL' : L = (L - 1) + 1 := by omega
        have hΛ' : Λ = (p : ℝ) ^ (((p : ℝ)⁻¹) ^ (L - 1)) := by
          rw [hΛ, hm]
          congr 1
          rw [Nat.cast_pow, ← inv_pow]
        rw [hn₀eq, hL', B_pow_succ, hΛ']

end AXL
end P2MW.S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le
