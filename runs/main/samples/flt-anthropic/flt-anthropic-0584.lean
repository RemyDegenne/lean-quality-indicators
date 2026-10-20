namespace P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab

attribute [-instance] RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar

set_option autoImplicit false

noncomputable section

namespace R4TCSigma

p2m_reactivate

section

open MeasureTheory NumberField

open NumberField.AdelicHaar

open scoped ComplexConjugate

open MeasureTheory.Measure

open scoped ENNReal

open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace ConvolutionAssociativity

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

variable {K}

scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

theorem rightConv_sum_right (u : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) {n : ℕ}
    (F : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (hF : ∀ k, Continuous (F k)) (hFc : ∀ k, HasCompactSupport (F k)) :
    rightConv K u (∑ k, F k) = ∑ k, rightConv K u (F k) := by
  funext x
  simp only [rightConv, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum _ fun k _ =>
    ((huc.comp (continuous_const.mul continuous_id)).mul (hF k)).integrable_of_hasCompactSupport (hFc k).mul_left

end ConvolutionAssociativity
end
end R4TCSigma
end
end P2MW.S_AutomorphicForm_integrableOn_twistedConvOp_mul_conj_and_summable_setIntegral_norm_finsum_twistedConvOp_mul_conj_of_orthonormal_of_isFundamentalDomain_slab
