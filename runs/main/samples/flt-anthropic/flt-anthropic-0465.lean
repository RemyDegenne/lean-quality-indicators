namespace P2MW.S_ModularCurve_MultCovering_infChart_chartData_goodFamily

attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite

attribute [-instance] WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

set_option autoImplicit false

p2m_open

namespace ModularCurve

namespace MultCovering

namespace LineAlg

p2m_open

open Polynomial

variable {K : Type*} [Field K]

theorem exists_natDegree_sub_eq {ι : Type*} {m : ℕ} (hm : 2 ≤ m) (P : ι → K[X])
    (hspan : Submodule.span K (Set.range P) = Polynomial.degreeLT K m)
    (c : ι) (hc : (P c).natDegree = m - 1) (hc0 : P c ≠ 0) :
    ∃ j, P j - C ((P j).coeff (m - 1) / (P c).leadingCoeff) * P c ≠ 0 ∧
      (P j - C ((P j).coeff (m - 1) / (P c).leadingCoeff) * P c).natDegree = m - 2 := by
  have hlc : (P c).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hc0
  have hlc' : (P c).coeff (m - 1) = (P c).leadingCoeff := by rw [Polynomial.leadingCoeff, hc]

  let π : K[X] →ₗ[K] K[X] :=
    LinearMap.id - LinearMap.smulRight (Polynomial.lcoeff K (m - 1)) ((P c).leadingCoeff⁻¹ • P c)
  have hπ : ∀ Q : K[X], π Q = Q - C (Q.coeff (m - 1) / (P c).leadingCoeff) * P c := by
    intro Q
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, Polynomial.lcoeff_apply,
      smul_smul, Polynomial.C_mul', div_eq_mul_inv]
  have hπlt : ∀ Q ∈ Polynomial.degreeLT K m, π Q ∈ Polynomial.degreeLT K (m - 1) := by
    intro Q hQ
    rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero] at hQ ⊢
    intro k hk
    rw [hπ, coeff_sub, coeff_C_mul]
    rcases Nat.lt_or_ge k m with hkm | hkm
    · have hk' : k = m - 1 := by omega
      subst hk'
      rw [hlc', div_mul_cancel₀ _ hlc, sub_self]
    · rw [hQ k hkm]
      have h0 : (P c).coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt; omega
      rw [h0, mul_zero, sub_zero]
  have hπfix : ∀ Q ∈ Polynomial.degreeLT K (m - 1), π Q = Q := by
    intro Q hQ
    rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero] at hQ
    rw [hπ, hQ (m - 1) le_rfl, zero_div, C_0, zero_mul, sub_zero]
  by_contra h
  push_neg at h
  have hsmall : ∀ j, π (P j) ∈ Polynomial.degreeLT K (m - 2) := by
    intro j
    have hj : π (P j) ∈ Polynomial.degreeLT K (m - 1) :=
      hπlt _ (by rw [← hspan]; exact Submodule.subset_span ⟨j, rfl⟩)
    rw [Polynomial.mem_degreeLT] at hj ⊢
    by_cases h0 : π (P j) = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree h0] at hj ⊢
      have h1 : (π (P j)).natDegree < m - 1 := by exact_mod_cast hj
      have h2 : (π (P j)).natDegree ≠ m - 2 := by
        have h0' : P j - C ((P j).coeff (m - 1) / (P c).leadingCoeff) * P c ≠ 0 := by rw [← hπ]; exact h0
        rw [hπ]; exact h j h0'
      exact_mod_cast (show (π (P j)).natDegree < m - 2 by omega)
  have hmap : ∀ Q ∈ Submodule.span K (Set.range P), π Q ∈ Polynomial.degreeLT K (m - 2) := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hsmall j
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hX : (X ^ (m - 2) : K[X]) ∈ Submodule.span K (Set.range P) := by
    rw [hspan]; exact X_pow_mem_degreeLT (by omega)
  have h1 := hmap _ hX
  rw [hπfix _ (X_pow_mem_degreeLT (by omega)), Polynomial.mem_degreeLT, degree_X_pow] at h1
  exact lt_irrefl _ (by exact_mod_cast h1)

end LineAlg
end MultCovering
end ModularCurve
end P2MW.S_ModularCurve_MultCovering_infChart_chartData_goodFamily
