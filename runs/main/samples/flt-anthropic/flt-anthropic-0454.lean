namespace P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge

attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 4000000

set_option linter.unreachableTactic false

set_option linter.unusedTactic false

set_option linter.unusedVariables false

set_option autoImplicit false

open UpperHalfPlane Filter AlgebraicCurve ModularCurve

open scoped Topology MatrixGroups ModularForm Pointwise

p2m_reactivate

set_option autoImplicit false

open UpperHalfPlane Filter AlgebraicCurve ModularCurve

open scoped Topology

open scoped ComplexConjugate MatrixGroups

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 8000000

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace PLBSEP

open CUSPATLAS ATLINT GLUE PLB

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem two_le_r (s : Fin r → FB N) (hs : IsEmbBasis N s) : 2 ≤ r := by
  classical
  have hr := L2.r_pos N s hs
  by_contra hlt
  push_neg at hlt
  have hr1 : r = 1 := by omega
  obtain ⟨v, hv⟩ := exists_place_ne_cuspInftyBar (N := N)
  obtain ⟨f, hf0, hfL, hford⟩ := PLBALG.exists_mem_riemannRochSpace_ord_add_eq_one N v
  have hEv : embDivisor N v = 0 := by simp [embDivisor, Finsupp.single_apply, Ne.symm hv]
  rw [hEv, add_zero] at hford
  have h1L : (1 : FB N) ∈ riemannRochSpace (embDivisor N) := by
    rw [mem_riemannRochSpace_iff]
    intro w; right
    rw [w.ord_one, neg_nonpos]
    simp only [embDivisor, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs <;> simp

  subst hr1
  set i₀ : Fin 1 := 0
  have hspan : ∀ g ∈ riemannRochSpace (embDivisor N), ∃ a : AlgebraicClosure ℚ,
      g = algebraMap (AlgebraicClosure ℚ) (FB N) a * s i₀ := by
    intro g hg
    rw [← hs.2] at hg
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hg
    refine ⟨c i₀, ?_⟩
    rw [← hc, Fin.sum_univ_one, Algebra.smul_def]
  obtain ⟨a, ha⟩ := hspan 1 h1L
  obtain ⟨b, hb⟩ := hspan f hfL
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [map_zero, zero_mul] at ha; exact one_ne_zero ha
  have hA0 : algebraMap (AlgebraicClosure ℚ) (FB N) a ≠ 0 := (map_ne_zero _).mpr ha0
  have hf : f = algebraMap (AlgebraicClosure ℚ) (FB N) (b / a) := by
    rw [map_div₀, eq_div_iff hA0]
    calc f * algebraMap (AlgebraicClosure ℚ) (FB N) a
        = algebraMap (AlgebraicClosure ℚ) (FB N) b * (algebraMap (AlgebraicClosure ℚ) (FB N) a * s i₀) := by rw [hb]; ring
      _ = algebraMap (AlgebraicClosure ℚ) (FB N) b := by rw [← ha, mul_one]
  have hba : b / a ≠ 0 := by
    intro h0; apply hf0; rw [hf, h0, map_zero]
  rw [hf, PLBALG.ord_algebraMap_eq_zero v hba] at hford
  exact zero_ne_one hford

end PLBSEP
end
end P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge
