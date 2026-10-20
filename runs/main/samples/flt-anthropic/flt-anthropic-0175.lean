namespace P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_mul_ideleNorm_det_rpow_principalLevel_and_levelOne_of_isFundamentalDomain_slab

attribute [-instance] instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open IsDedekindDomain AutomorphicForm NumberField.TateGlobal HeckePair HeckeIntegralSeam AdelicDock LocalGL2

open scoped NNReal Pointwise ENNReal

noncomputable section

namespace R4ModTwist

section Transfer

variable {G H : Type*} [Group G] [Group H]

variable (ι : H →* G) (loc : G →* H) (U : Subgroup G) (K : Subgroup H)

theorem isHeckeCosetSystem_comp (hli : ∀ h, loc (ι h) = h) (hUK : ∀ u ∈ U, loc u ∈ K)
    (hKU : ∀ k ∈ K, ι k ∈ U)
    (hfac : ∀ u ∈ U, ∃ k ∈ K, ∃ u' ∈ U, u = ι k * u' ∧ ∀ h : H, ι h * u' = u' * ι h)
    {P : H} {κ : Type*} {ε : κ → H} (hε : IsHeckeCosetSystem K P ε) :
    IsHeckeCosetSystem U (ι P) (fun i => ι (ε i)) := by
  refine ⟨fun i => ?_, fun x hx => ?_, fun i j hij => ?_⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := mem_doubleCoset_iff.mp (hε.mem_doubleCoset i)
    refine mem_doubleCoset_iff.mpr ⟨ι u, hKU u hu, ι v, hKU v hv, ?_⟩
    rw [← map_mul, ← map_mul, huv]
  · obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := mem_doubleCoset_iff.mp hx
    obtain ⟨k, hk, u', hu', rfl, hcomm⟩ := hfac u₁ hu₁
    have hkP : k * P ∈ doubleCoset K P := mem_doubleCoset_iff.mpr ⟨k, hk, 1, one_mem _, by rw [mul_one]⟩
    obtain ⟨i, hi⟩ := hε.covers _ hkP
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    have h1 : ι k * u' * ι P * u₂ = ι (k * P) * (u' * u₂) := by
      rw [map_mul, mul_assoc (ι k) u', ← hcomm P]; simp only [mul_assoc]
    rw [h1, mul_inv_rev, mul_assoc]
    refine mul_mem (inv_mem (mul_mem hu' hu₂)) ?_
    have := hKU _ hi
    rwa [map_mul, map_inv] at this
  · apply hε.mk_injective
    have hij' : (QuotientGroup.mk (ι (ε i)) : G ⧸ U) = QuotientGroup.mk (ι (ε j)) := hij
    rw [QuotientGroup.eq] at hij' ⊢
    have := hUK _ hij'
    rwa [← map_inv, ← map_mul, hli] at this

end Transfer
end R4ModTwist
end
end P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_mul_ideleNorm_det_rpow_principalLevel_and_levelOne_of_isFundamentalDomain_slab
