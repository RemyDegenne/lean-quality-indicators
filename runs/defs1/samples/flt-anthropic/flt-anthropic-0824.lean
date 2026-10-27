namespace P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two

attribute [-instance] RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open MeasureTheory Set NumberField IsDedekindDomain NumberField.TateGlobal Matrix

open scoped ENNReal NNReal Pointwise TensorProduct TensorProduct.RightActions

noncomputable section

namespace P2mCentralCovolQuat

section Setting

p2m_open

open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

abbrev δA (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
  Matrix.GeneralLinearGroup.map (inclA K L) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c

end Setting
end P2mCentralCovolQuat
end
end P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two
