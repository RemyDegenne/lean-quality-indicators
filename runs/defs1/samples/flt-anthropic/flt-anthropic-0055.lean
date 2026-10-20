namespace P2MW.S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 320000

open NumberField IsDedekindDomain MeasureTheory Set Function

open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace KcSemiLocalIwasawaHaar

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K

local notation "E" => L ⊗[K] v.adicCompletion K

local notation "Q" => (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)

local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule

attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  isScalarTower_FEE smulCommClass_FEE finite_KL

attribute [local instance] secondCountableTopology_E

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_GL
  isTopologicalGroup_GL measurableSpace_GL

attribute [local instance] borelSpace_GL isHaarMeasure_semiLocalHaar

attribute [local instance] measurableMul_GL measurableInv_GL

local notation "μG" => AutomorphicForm.semiLocalHaar K L v

local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v

local notation "𝒪" => AutomorphicForm.semiLocalIntegers K L v

section TwShift

variable (σ : L ≃ₐ[K] L)

def Theta (z : (Fˣ × Fˣ) × (E × G)) : G :=
  (AutomorphicForm.sigmaGL K L F σ z.2.2)⁻¹ *
    ((nGL (AutomorphicForm.sigmaTensor K L F σ z.2.1))⁻¹ *
      AutomorphicForm.toTensorGL K L F (diagUnits2 z.1.1 z.1.2) * nGL (AutomorphicForm.sigmaTensor K L F σ z.2.1)) *
    AutomorphicForm.sigmaGL K L F σ z.2.2

end TwShift
end KcSemiLocalIwasawaHaar
end
end P2MW.S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal
