namespace P2MW.S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

set_option maxHeartbeats 3200000

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicVolume NumberField.TateGlobal MeasureTheory

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open scoped ENNReal NNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace K1aOfFinite

variable {F : Type} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

local notation "𝔾" => AdelicGL2 (𝓞 F) F

local notation "Γp" => MonoidHom.range (globalPoints (𝓞 F) F)

local notation "μH" => adelicGLHaar (Fin 2) (𝓞 F) F

theorem det_globalPoints (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ) =
      Units.map (algebraMap F 𝔸).toMonoidHom (Matrix.GeneralLinearGroup.det γ) := by
  unfold globalPoints
  rw [Matrix.GeneralLinearGroup.map_det]
  rfl

end K1aOfFinite
end
end P2MW.S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite
