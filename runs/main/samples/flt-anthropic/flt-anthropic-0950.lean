namespace P2MW.S_UnipotentTermUnfolding_exists_forall_integrableOn_and_lintegral_ne_top_and_setIntegral_unipotentTerm_eq_mul_integral_iwasawa_of_isSemiLocalFactorization

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions

set_option autoImplicit false

set_option Elab.async false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open IsDedekindDomain

p2m_open

open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

section TwistedBruhatProofs

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open IsDedekindDomain

p2m_open

open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace AutomorphicForm

namespace TwistedBruhat

p2m_open

section Bruhat

open LT.TwistedNorm

open scoped Matrix

theorem mulVec_eq_smul_iff {L : Type} [Field L] (M : Matrix (Fin 2) (Fin 2) L) (w : Fin 2 → L) (c : L) :
    M *ᵥ w = c • w ↔ M 0 0 * w 0 + M 0 1 * w 1 = c * w 0 ∧ M 1 0 * w 0 + M 1 1 * w 1 = c * w 1 := by
  constructor
  · intro h
    exact ⟨by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 0,
      by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]

end Bruhat
end TwistedBruhat
end AutomorphicForm
end TwistedBruhatProofs
end P2MW.S_UnipotentTermUnfolding_exists_forall_integrableOn_and_lintegral_ne_top_and_setIntegral_unipotentTerm_eq_mul_integral_iwasawa_of_isSemiLocalFactorization
