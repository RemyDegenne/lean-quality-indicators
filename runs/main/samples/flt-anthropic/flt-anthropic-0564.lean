namespace P2MW.S_NumberField_StandardAddChar_psiLocal_rat_eq_psiQ_adeleSingleAt

set_option autoImplicit false

open NumberField NumberField.StandardAddChar IsDedekindDomain

namespace PSIBAux

open NumberField.AdelicTrace

theorem algebraMap_trace_ringOfIntegers_rat (a : 𝓞 ℚ) :
    algebraMap ℤ (𝓞 ℚ) (Algebra.trace ℤ (𝓞 ℚ) a) = a := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, algebraMap ℤ (𝓞 ℚ) n = a :=
    ⟨Rat.ringOfIntegersEquiv a, by
      apply Rat.ringOfIntegersEquiv.injective
      simp⟩
  rw [Algebra.trace_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, one_smul]

end PSIBAux
end P2MW.S_NumberField_StandardAddChar_psiLocal_rat_eq_psiQ_adeleSingleAt
