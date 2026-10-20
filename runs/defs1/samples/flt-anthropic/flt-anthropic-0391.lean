namespace P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_and_summable_setIntegral_norm_finsum_convOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab

attribute [-instance] RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar

set_option autoImplicit false

noncomputable section

namespace R4TCSigma

section

open MeasureTheory NumberField

open NumberField.AdelicHaar

open scoped ComplexConjugate

open MeasureTheory.Measure

open scoped ENNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace Venue

open AutomorphicForm NumberField.TateGlobal NumberField.AdelicVolume

variable (K : Type) [Field K] [NumberField K]

variable {K}

scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

scoped instance instMeasurableConstSMulΓ : MeasurableConstSMul (Γ K) (AdelicGL2 (𝓞 K) K) :=
  ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩

def ven (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) :
    Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) where
  carrier := {φ | Continuous φ ∧ IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ MemLp φ 2 ((μ K).restrict Φ₀)}
  zero_mem' := ⟨continuous_zero, ⟨fun _ _ => rfl, fun _ _ => by simp⟩, MemLp.zero'⟩
  add_mem' := by
    rintro φ ψ ⟨hφc, hφ, hφ₂⟩ ⟨hψc, hψ, hψ₂⟩
    exact ⟨hφc.add hψc,
      ⟨fun γ g => by simp only [Pi.add_apply, hφ.left_invariant, hψ.left_invariant],
        fun z g => by simp only [Pi.add_apply, hφ.central_transform, hψ.central_transform, mul_add]⟩,
      hφ₂.add hψ₂⟩
  smul_mem' := by
    rintro c φ ⟨hφc, hφ, hφ₂⟩
    exact ⟨hφc.const_smul c,
      ⟨fun γ g => by simp only [Pi.smul_apply, hφ.left_invariant],
        fun z g => by simp only [Pi.smul_apply, smul_eq_mul, hφ.central_transform]; ring⟩,
      hφ₂.const_smul c⟩

end Venue
end
end R4TCSigma
end
end P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_and_summable_setIntegral_norm_finsum_convOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
