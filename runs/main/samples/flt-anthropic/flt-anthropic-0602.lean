namespace P2MW.S_AutomorphicForm_RankinSelberg_analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery

attribute [-instance] instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

p2m_open

open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open Filter Topology

noncomputable section

namespace AutomorphicForm

p2m_open

namespace TDSPAssembly

variable (K : Type) [Field K] [NumberField K]

scoped instance : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

scoped instance secondCountableTopology_maxCpt : SecondCountableTopology (adelicMaximalCompact K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

scoped instance : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K

scoped instance secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompactSpace_idele : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar K) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  infer_instance

scoped instance sFinite_sPartMeasure (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SFinite (NumberField.Idele.sPartMeasure K S) := by
  unfold NumberField.Idele.sPartMeasure; infer_instance

section RealBook

variable {K}

theorem rpow_le_min_rpow_mul_max_rpow {r e e₁ e₂ : ℝ} (hr : 0 < r) (h₁ : e₁ ≤ e) (h₂ : e ≤ e₂) :
    r ^ e ≤ (min 1 r) ^ e₁ * (max 1 r) ^ e₂ := by
  rcases le_total r 1 with hr1 | hr1
  · rw [min_eq_right hr1, max_eq_left hr1, Real.one_rpow, mul_one]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 h₁
  · rw [min_eq_left hr1, max_eq_right hr1, Real.one_rpow, one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hr1 h₂

end RealBook
end TDSPAssembly
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_RankinSelberg_analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery
