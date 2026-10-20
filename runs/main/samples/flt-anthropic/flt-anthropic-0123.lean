namespace P2MW.S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat

attribute [-instance] instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

p2m_open

open NumberField.TateGlobal AutomorphicForm AutomorphicForm.WindowedSiegel

open Set Filter Topology IsDedekindDomain

open scoped NNReal

noncomputable section

namespace NumberField

namespace AdelicFourier

namespace GodementSiegelEstimate

p2m_open

variable {F : Type} [Field F] [NumberField F]

theorem real_bound (C c D : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hD : 0 < D) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r α δ H : ℝ), 1 ≤ r → 0 < α → 0 < δ → D ≤ α * δ → α / δ = H → c ≤ H →
      C * (1 + (r * α)⁻¹ ^ 2) * (1 + (r * δ)⁻¹ ^ 2) * (min 1 ((r * α)⁻¹ ^ N) + min 1 ((r * δ)⁻¹ ^ N))
        ≤ B * (1 + H) ^ (N + 1) * r⁻¹ ^ N := by
  set e : ℝ := (Real.sqrt (c * D))⁻¹ with he_def
  set d : ℝ := (Real.sqrt D)⁻¹ with hd_def
  have he : 0 ≤ e := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hd : 0 ≤ d := inv_nonneg.2 (Real.sqrt_nonneg _)
  refine ⟨C * (1 + e ^ 2) * (1 + D⁻¹) * (e ^ N + d ^ N), by positivity, ?_⟩
  intro r α δ H hr hα hδ hDαδ hHdef hcH
  have hH : 0 < H := hc.trans_le hcH
  have hr0 : 0 < r := one_pos.trans_le hr

  have hα2 : c * D ≤ α ^ 2 := by
    have : α ^ 2 = H * (α * δ) := by rw [← hHdef]; field_simp
    rw [this]
    exact mul_le_mul hcH hDαδ hD.le hH.le
  have hαinv : α⁻¹ ≤ e := by
    have h1 : Real.sqrt (c * D) ≤ α := by
      have := Real.sqrt_le_sqrt hα2
      rwa [Real.sqrt_sq hα.le] at this
    exact inv_anti₀ (Real.sqrt_pos.2 (mul_pos hc hD)) h1
  have hδ2 : D ≤ δ ^ 2 * H := by
    have : δ ^ 2 * H = α * δ := by rw [← hHdef]; field_simp
    rw [this]; exact hDαδ
  have hδinv2 : δ⁻¹ ^ 2 ≤ H / D := by
    rw [inv_pow, le_div_iff₀ hD, inv_mul_le_iff₀ (pow_pos hδ 2)]
    exact hδ2
  have hδinv : δ⁻¹ ≤ (1 + H) * d := by
    have h1 : δ⁻¹ ≤ Real.sqrt (H / D) := by
      rw [← Real.sqrt_sq (inv_nonneg.2 hδ.le)]
      exact Real.sqrt_le_sqrt hδinv2
    have h2 : Real.sqrt (H / D) = Real.sqrt H * d := by
      rw [hd_def, Real.sqrt_div' _ hD.le, div_eq_mul_inv]
    refine h1.trans ?_
    rw [h2]
    exact mul_le_mul_of_nonneg_right (sqrt_le_one_add hH.le) hd

  have hrα : (r * α)⁻¹ ≤ α⁻¹ := by
    refine inv_anti₀ hα ?_
    calc α = 1 * α := (one_mul α).symm
      _ ≤ r * α := mul_le_mul_of_nonneg_right hr hα.le
  have hrδ : (r * δ)⁻¹ ≤ δ⁻¹ := by
    refine inv_anti₀ hδ ?_
    calc δ = 1 * δ := (one_mul δ).symm
      _ ≤ r * δ := mul_le_mul_of_nonneg_right hr hδ.le
  have hrαnn : 0 ≤ (r * α)⁻¹ := inv_nonneg.2 (mul_nonneg hr0.le hα.le)
  have hrδnn : 0 ≤ (r * δ)⁻¹ := inv_nonneg.2 (mul_nonneg hr0.le hδ.le)
  have hT1 : 1 + (r * α)⁻¹ ^ 2 ≤ 1 + e ^ 2 := by
    have : (r * α)⁻¹ ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ hrαnn (hrα.trans hαinv) 2
    linarith
  have hT2 : 1 + (r * δ)⁻¹ ^ 2 ≤ (1 + D⁻¹) * (1 + H) := by
    have h1 : (r * δ)⁻¹ ^ 2 ≤ H / D := (pow_le_pow_left₀ hrδnn hrδ 2).trans hδinv2
    have h2 : 1 + H / D ≤ (1 + D⁻¹) * (1 + H) := by
      have : (1 + D⁻¹) * (1 + H) = 1 + H / D + (H + D⁻¹) := by rw [div_eq_mul_inv]; ring
      rw [this]
      linarith [inv_nonneg.2 hD.le]
    linarith
  have h1H : 1 ≤ 1 + H := by linarith
  have hT3 : min 1 ((r * α)⁻¹ ^ N) + min 1 ((r * δ)⁻¹ ^ N) ≤ (1 + H) ^ N * (e ^ N + d ^ N) * r⁻¹ ^ N := by
    have ha : min 1 ((r * α)⁻¹ ^ N) ≤ r⁻¹ ^ N * e ^ N := by
      refine (min_le_right _ _).trans ?_
      rw [mul_inv, mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 hα.le) hαinv N)
        (pow_nonneg (inv_nonneg.2 hr0.le) N)
    have hb : min 1 ((r * δ)⁻¹ ^ N) ≤ r⁻¹ ^ N * ((1 + H) ^ N * d ^ N) := by
      refine (min_le_right _ _).trans ?_
      rw [mul_inv, mul_pow, ← mul_pow (1 + H) d N]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 hδ.le) hδinv N)
        (pow_nonneg (inv_nonneg.2 hr0.le) N)
    have hc' : e ^ N ≤ (1 + H) ^ N * e ^ N := by
      calc e ^ N = 1 * e ^ N := (one_mul _).symm
        _ ≤ (1 + H) ^ N * e ^ N := mul_le_mul_of_nonneg_right (one_le_pow₀ h1H) (pow_nonneg he N)
    have hrN : 0 ≤ r⁻¹ ^ N := pow_nonneg (inv_nonneg.2 hr0.le) N
    calc min 1 ((r * α)⁻¹ ^ N) + min 1 ((r * δ)⁻¹ ^ N)
        ≤ r⁻¹ ^ N * e ^ N + r⁻¹ ^ N * ((1 + H) ^ N * d ^ N) := add_le_add ha hb
      _ ≤ r⁻¹ ^ N * ((1 + H) ^ N * e ^ N) + r⁻¹ ^ N * ((1 + H) ^ N * d ^ N) := by
          have := mul_le_mul_of_nonneg_left hc' hrN
          linarith
      _ = (1 + H) ^ N * (e ^ N + d ^ N) * r⁻¹ ^ N := by ring
  have hT2nn : 0 ≤ 1 + (r * δ)⁻¹ ^ 2 := by positivity
  have hT3nn : 0 ≤ min 1 ((r * α)⁻¹ ^ N) + min 1 ((r * δ)⁻¹ ^ N) :=
    add_nonneg (le_min zero_le_one (pow_nonneg hrαnn N)) (le_min zero_le_one (pow_nonneg hrδnn N))
  calc C * (1 + (r * α)⁻¹ ^ 2) * (1 + (r * δ)⁻¹ ^ 2) * (min 1 ((r * α)⁻¹ ^ N) + min 1 ((r * δ)⁻¹ ^ N))
      ≤ C * (1 + e ^ 2) * ((1 + D⁻¹) * (1 + H)) * ((1 + H) ^ N * (e ^ N + d ^ N) * r⁻¹ ^ N) := by
        gcongr
    _ = C * (1 + e ^ 2) * (1 + D⁻¹) * (e ^ N + d ^ N) * (1 + H) ^ (N + 1) * r⁻¹ ^ N := by ring

end GodementSiegelEstimate
end AdelicFourier
end NumberField
end
end P2MW.S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat
