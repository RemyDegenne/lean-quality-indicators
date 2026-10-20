namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion

set_option autoImplicit false

open IsLocalRing WithZero

open scoped IntermediateField

namespace AlgebraicCurve

p2m_open

namespace HolRingFGAux

section Main

open IntermediateField

open scoped IntermediateField.algebraAdjoinAdjoin

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable [IsAlgClosed k] [IsCurveOver k K] [Algebra.EssFiniteType k K]

theorem exists_fin_generators (N : Finset (Place k K)) (hN : N.Nonempty) :
    ∃ (n : ℕ) (z : Fin n → K),
      (∀ i, ∀ Q : Place k K, Q ∉ N → z i ∈ Q.toValuationSubring) ∧
      ∀ f : K, (∀ Q : Place k K, Q ∉ N → f ∈ Q.toValuationSubring) →
        f ∈ Algebra.adjoin k (Set.range z) := by
  classical
  obtain ⟨s, hs⟩ := holRing_fg N hN
  refine ⟨s.card, fun i => ((s.equivFin.symm i : ↥s) : K), fun i Q hQ => ?_, fun f hf => ?_⟩
  · have hmem : ((s.equivFin.symm i : ↥s) : K) ∈ holRing N := by
      rw [← hs]
      exact Algebra.subset_adjoin (s.equivFin.symm i).2
    exact mem_holRing_iff.mp hmem Q hQ
  · have hrange : Set.range (fun i : Fin s.card => ((s.equivFin.symm i : ↥s) : K)) = (↑s : Set K) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact (s.equivFin.symm i).2
      · intro hy
        exact ⟨s.equivFin ⟨y, hy⟩, by simp⟩
    rw [hrange, hs]
    exact mem_holRing_iff.mpr hf

end Main
end HolRingFGAux
end AlgebraicCurve
end P2MW.S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd
