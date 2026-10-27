namespace P2MW.S_AutomorphicForm_eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Set Function Matrix

open scoped ENNReal NNReal Classical

noncomputable section

namespace KcEllOrbUnfold

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K

local notation "Q" => v.adicCompletion K × v.adicCompletion K

local notation "P" => Fin 4 → v.adicCompletion K

local notation "G" => GL (Fin 2) (v.adicCompletion K)

attribute [local instance] t2Space_GL secondCountableTopology_GL
  AutomorphicForm.locallyCompactSpace_localGL
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.localCentralizerBorel AutomorphicForm.isHaarMeasure_localHaar

attribute [local instance] borelSpace_localCentralizer locallyCompactSpace_localCentralizer
  secondCountableTopology_localCentralizer

section Chain

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

local notation "π" => Measure.pi fun _ : Fin 4 => μ

local notation "μ²" => Measure.prod μ μ

variable {d : v.adicCompletion K} {u : GL (Fin 2) (v.adicCompletion K)}

variable (τ : Measure (AutomorphicForm.localCentralizer K v u)) [τ.IsHaarMeasure] {cG cT : ℝ≥0∞}

scoped instance sFinite_ρS : SFinite (ρS μ) := by unfold ρS; infer_instance

section Support

variable {p₀ r₀ : v.adicCompletion K}

def Λ (u : G) (f : G → ℂ) (q : Q) : ℂ := ‖q.2‖⁻¹ • fq u f q

end Support
end Chain
end KcEllOrbUnfold
end
end P2MW.S_AutomorphicForm_eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare
