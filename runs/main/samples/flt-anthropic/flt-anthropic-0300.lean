namespace P2MW.S_AutomorphicForm_lambdaT_finsum_integral_sigmaAdelicAct_eq_and_lambdaT_finsum_twistedConvOp_chiDet_eq_and_rightConv_mul_ideleNorm_det_rpow_eq

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

set_option maxHeartbeats 6400000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open IsDedekindDomain

open scoped TensorProduct Pointwise ComplexConjugate NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace R4DictSigma

open AutomorphicForm NumberField.TateGlobal

section IdeleAction

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]

theorem integral_comp_unitsAct (ν : Measure (AdeleRing (𝓞 L) L)ˣ) [ν.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (G : (AdeleRing (𝓞 L) L)ˣ → ℂ) :
    ∫ z, G (D.unitsAct σ z) ∂ν = ∫ z, G z ∂ν := by
  have hmp : MeasurePreserving (unitsActHomeo D σ).toMeasurableEquiv ν ν := measurePreserving_unitsAct ν D σ
  exact hmp.integral_comp' G

end IdeleAction
end R4DictSigma
end
end P2MW.S_AutomorphicForm_lambdaT_finsum_integral_sigmaAdelicAct_eq_and_lambdaT_finsum_twistedConvOp_chiDet_eq_and_rightConv_mul_ideleNorm_det_rpow_eq
