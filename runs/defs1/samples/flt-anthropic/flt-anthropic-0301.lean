namespace P2MW.S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra

set_option autoImplicit false

p2m_open

open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace AutomorphicForm

p2m_open

namespace IwasawaCoord

variable (K : Type) [Field K] [NumberField K]

scoped instance : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

scoped instance secondCountableTopology_borel : SecondCountableTopology (adelicBorel (𝓞 K) K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

scoped instance secondCountableTopology_maxCpt : SecondCountableTopology (adelicMaximalCompact K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

scoped instance locallyCompactSpace_borel : LocallyCompactSpace (adelicBorel (𝓞 K) K) := (isClosed_adelicBorel K).locallyCompactSpace

scoped instance action : MulAction (L K) (AdelicGL2 (𝓞 K) K) where
  smul l g := (l.1 : AdelicGL2 (𝓞 K) K) * g * ((l.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹
  one_smul g := by
    change ((1 : adelicBorel (𝓞 K) K) : AdelicGL2 (𝓞 K) K) * g * (((1 : adelicMaximalCompact K)) : AdelicGL2 (𝓞 K) K)⁻¹ = g
    simp
  mul_smul l l' g := by
    change ((l * l').1 : AdelicGL2 (𝓞 K) K) * g * (((l * l').2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹ =
      (l.1 : AdelicGL2 (𝓞 K) K) * ((l'.1 : AdelicGL2 (𝓞 K) K) * g * ((l'.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹) *
        ((l.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev]
    group

scoped instance continuousSMul : ContinuousSMul (L K) (AdelicGL2 (𝓞 K) K) := by
  refine ⟨?_⟩
  change Continuous fun p : L K × AdelicGL2 (𝓞 K) K =>
    (p.1.1 : AdelicGL2 (𝓞 K) K) * p.2 * ((p.1.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹
  exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_snd).mul
    (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv

scoped instance isPretransitive : MulAction.IsPretransitive (L K) (AdelicGL2 (𝓞 K) K) := by
  refine ⟨fun g₁ g₂ => ?_⟩
  obtain ⟨l₁, h₁⟩ := exists_smul_one_eq K g₁
  obtain ⟨l₂, h₂⟩ := exists_smul_one_eq K g₂
  exact ⟨l₂ * l₁⁻¹, by rw [← h₁, ← h₂, mul_smul, inv_smul_smul]⟩

scoped instance compactSpace_BK : CompactSpace (BK K) := by
  refine isCompact_iff_compactSpace.mp ?_
  exact ((isClosed_adelicBorel K).preimage continuous_subtype_val).isCompact

scoped instance isInvInvariant_maximalCompactHaar : (maximalCompactHaar K).IsInvInvariant :=
  isInvInvariant_of_compactSpace (maximalCompactHaar K)

scoped instance : (borelHaar K).IsHaarMeasure := by unfold borelHaar; infer_instance

scoped instance sigmaFinite_borelHaar : SigmaFinite (borelHaar K) := by
  haveI : SigmaCompactSpace (adelicBorel (𝓞 K) K) := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

scoped instance sigmaFinite_maximalCompactHaar : SigmaFinite (maximalCompactHaar K) := inferInstance

def LHaar : Measure (L K) := (borelHaar K).prod (maximalCompactHaar K)

end IwasawaCoord
end AutomorphicForm
end
end P2MW.S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
