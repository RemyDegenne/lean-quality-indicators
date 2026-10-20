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

scoped instance countable_gl2 : Countable (GL (Fin 2) F) := by
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  refine Function.Injective.countable
    (f := fun g : GL (Fin 2) F => fun i j => (g : Matrix (Fin 2) (Fin 2) F) i j) ?_
  intro a b h
  exact Matrix.GeneralLinearGroup.ext fun i j => congrFun (congrFun h i) j

scoped instance countable_range : Countable Γp :=
  Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 F) F))

variable (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)

variable {ξ}

def rt (A : Set 𝔾) (x : 𝔾) : Set 𝔾 := (fun y => y * x⁻¹) ⁻¹' A

end K1aOfFinite
end
end P2MW.S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite
