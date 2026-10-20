namespace P2MW.S_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

noncomputable section

p2m_open

open scoped Manifold ContDiff Topology

namespace AlgebraicCurve

namespace AbelNecessityProof

p2m_open

theorem sub_mem_of_eventually_sub_mem {X M : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [AddCommGroup M] (L : AddSubgroup M) (φ : X → M)
    (h : ∀ x₀ : X, ∀ᶠ x in 𝓝 x₀, φ x - φ x₀ ∈ L) (x y : X) : φ x - φ y ∈ L := by
  let S : Set X := {x | φ x - φ y ∈ L}
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [h x] with x' hx'
    have : φ x' - φ y = (φ x' - φ x) + (φ x - φ y) := by abel
    show φ x' - φ y ∈ L
    rw [this]
    exact L.add_mem hx' hx
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [h x] with x' hx' hxS
    apply hx
    have : φ x - φ y = (φ x' - φ y) - (φ x' - φ x) := by abel
    show φ x - φ y ∈ L
    rw [this]
    exact L.sub_mem hxS hx'
  have hy : y ∈ S := by
    show φ y - φ y ∈ L
    rw [sub_self]
    exact L.zero_mem
  have hS : S = Set.univ := by
    rcases isClopen_iff.1 ⟨hclosed, hopen⟩ with h0 | h1
    · exact absurd (h0 ▸ hy : y ∈ (∅ : Set X)) (Set.notMem_empty y)
    · exact h1
  have hx : x ∈ S := by rw [hS]; exact Set.mem_univ x
  exact hx

end AbelNecessityProof
end AlgebraicCurve
end
end P2MW.S_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal
