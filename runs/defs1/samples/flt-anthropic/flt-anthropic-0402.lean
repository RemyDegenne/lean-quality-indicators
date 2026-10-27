namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_norm_sq_deriv_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section ArchNormalisedFactor

namespace ArchNormalisedFactor

open Complex

noncomputable def cplxNorm (a b m M : ℕ) (u s : ℂ) : ℂ :=
  if a = b then
    ((a.factorial : ℕ) : ℂ) / 2 *
      (if m = 2 * a ∧ M = 0 then
        Complex.Gamma (2 * s + u + 1) * (Complex.Gamma (2 * s + u + 1 + (a : ℂ)))⁻¹
      else
        (2 * s + u + (M : ℂ) / 2) * Complex.Gamma (2 * s + u + (m : ℂ) / 2 - (a : ℂ)) *
          (Complex.Gamma (2 * s + u + (m : ℂ) / 2 + 1))⁻¹)
  else 0

end ArchNormalisedFactor
end ArchNormalisedFactor
end P2MW.S_AutomorphicForm_exists_forall_lintegral_norm_sq_deriv_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat
