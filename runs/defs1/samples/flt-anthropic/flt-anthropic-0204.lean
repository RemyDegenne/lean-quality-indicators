namespace P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd

attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped TensorProduct Polynomial

open scoped TensorProduct.RightActions

namespace InertProof

open AutomorphicForm

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace InertAssembly

noncomputable scoped instance finite_valuedResidueField
    (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    Finite (Valued.ResidueField (w.adicCompletion L)) :=
  inferInstanceAs (Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers L)))

p2m_reactivate

section Local

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

noncomputable def sA (σ : L ≃ₐ[K] L) :
    (L ⊗[K] v.adicCompletion K) →ₐ[v.adicCompletion K] (L ⊗[K] v.adicCompletion K) :=
  { AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ with
    commutes' := by
      intro a
      show AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ (1 ⊗ₜ a) = 1 ⊗ₜ a
      simp [AutomorphicForm.sigmaTensor] }

end Local
end InertAssembly
end InertProof
end P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd
