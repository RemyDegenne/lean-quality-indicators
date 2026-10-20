namespace P2MW.S_AutomorphicForm_lintegral_lintegral_adelicWeyl_mul_unipotentGL2_mul_eq_of_forall_centralScalar_mul_diagOne_mul_eq

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm

open scoped ENNReal NNReal Pointwise Topology

noncomputable section

namespace R4W3

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

local notation "G" => AdelicGL2 (𝓞 F) F

local notation "I" => (AdeleRing (𝓞 F) F)ˣ

local notation "KK" => adelicMaximalCompact F

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

scoped instance secondCountable_adele : SecondCountableTopology 𝔸 :=
  NumberField.AdeleRing.secondCountableTopology F

scoped instance secondCountable_gl : SecondCountableTopology G :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F

scoped instance secondCountable_mulOpposite_adele : SecondCountableTopology 𝔸ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountable_idele : SecondCountableTopology I :=
  Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompactSpace_idele : LocallyCompactSpace I :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance isAddHaarMeasure_adelicAddHaar' : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure :=
  isAddHaarMeasure_adelicAddHaar (𝓞 F) F

scoped instance isHaarMeasure_adelicGLHaar' : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

scoped instance regular_adelicAddHaar : (adelicAddHaar (𝓞 F) F).Regular := by
  show Measure.Regular (Measure.addHaar)
  unfold Measure.addHaar
  infer_instance

scoped instance regular_idelicHaar : (NumberField.Idele.idelicHaar F).Regular := by
  show Measure.Regular (Measure.haar)
  unfold Measure.haar
  infer_instance

local notation "dx" => adelicAddHaar (𝓞 F) F

local notation "dI" => NumberField.Idele.idelicHaar F

local notation "dT" => Measure.prod (NumberField.Idele.idelicHaar F) (NumberField.Idele.idelicHaar F)

local notation "dk" => AutomorphicForm.maximalCompactHaar F

local notation "dq" => Measure.prod (AutomorphicForm.maximalCompactHaar F) (adelicAddHaar (𝓞 F) F)

local notation "dg" => adelicGLHaar (Fin 2) (𝓞 F) F

def Haux (Φ : G → ℝ≥0∞) (z : 𝔸 × (I × I)) : ℝ≥0∞ :=
  (∫⁻ k, Φ (tau F z.2 * (unipotentGL2 ((((z.2.2)⁻¹ : I) : 𝔸) * z.1) * (k : G))) ∂dk) * (nrm F z.2.2)⁻¹

end R4W3
end
end P2MW.S_AutomorphicForm_lintegral_lintegral_adelicWeyl_mul_unipotentGL2_mul_eq_of_forall_centralScalar_mul_diagOne_mul_eq
