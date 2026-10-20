namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one_of_forall_lt_finrank

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain

open scoped TensorProduct

noncomputable section

namespace R4S30LocalIndexGen

section Uniformizer

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)

include hϖ

theorem irreducible_piO : Irreducible (piO K v ϖ hϖ) := by
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [isUnit_int_iff, coe_piO, v_pi K v ϖ hϖ, ← WithZero.exp_zero]
    intro h
    have := WithZero.exp_injective h
    omega
  · have hv : (Valued.v (a : v.adicCompletion K) : WithZero (Multiplicative ℤ)) * Valued.v (b : v.adicCompletion K) =
        WithZero.exp (-1) := by
      rw [← map_mul, ← v_pi K v ϖ hϖ, ← coe_piO K v ϖ hϖ, hab]; rfl
    by_cases ha : IsUnit a
    · exact Or.inl ha
    · right
      have ha' : (Valued.v (a : v.adicCompletion K) : WithZero (Multiplicative ℤ)) < 1 :=
        (Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := a)).1 ha
      have ha'' := le_exp_neg_one_of_lt_one ha'
      have hb1 : (Valued.v (b : v.adicCompletion K) : WithZero (Multiplicative ℤ)) ≤ 1 := b.2
      rw [isUnit_int_iff]
      refine le_antisymm hb1 ?_
      by_contra hlt
      push Not at hlt
      have hlt' : (Valued.v (a : v.adicCompletion K) : WithZero (Multiplicative ℤ)) * Valued.v (b : v.adicCompletion K) <
          WithZero.exp (-1) * 1 := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos ha'' hlt zero_le' WithZero.exp_pos
      rw [mul_one, hv] at hlt'
      exact lt_irrefl _ hlt'

end Uniformizer
end R4S30LocalIndexGen
end
end P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one_of_forall_lt_finrank
