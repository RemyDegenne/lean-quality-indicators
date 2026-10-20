namespace P2MW.S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

universe u

noncomputable section

namespace P2mKcZp2Matrix

variable (p : ℕ) [Fact p.Prime]

scoped instance instFintypeF : Fintype (F p) := Fintype.ofFinite _

theorem linearIndependent_one_ω : LinearIndependent (ZMod p) ![(1 : F p), ω p] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
    exact ⟨hst, rfl⟩
  · exfalso
    apply ω_spec p
    have hω : ω p = ι p (-(s / t)) := by
      have h1 : t • ω p = -(s • (1 : F p)) := eq_neg_of_add_eq_zero_right hst
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h1
      have ht' : ι p t ≠ 0 := by
        intro h0; exact ht ((map_eq_zero_iff _ (algebraMap (ZMod p) (F p)).injective).mp h0)
      field_simp
      rw [map_neg, map_div₀]
      field_simp
      linear_combination h1
    rw [hω, pow_p_algebraMap]

end P2mKcZp2Matrix
end
end P2MW.S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul
