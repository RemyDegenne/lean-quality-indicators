namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_gl3Translates_sum_rsFinIntegral_cells_eq_const_and_dual_eq_rootNumberMonomial_of_finWhittaker_one_ne_zero_of_localSpaceAt_of_member_of_fe32_normPin_twisted_offSQ_archPsi_bump_levelShift_global

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SmoothVectors.nonarchimedeanGroup_gl2Padic FLT.SpectralSide.instCompactSpaceMatrix LocalGL2.Kirillov.fintype_Qm LocalGL2.Kirillov.fintype_Ch LocalGL2.Kirillov.addCommGroup_Ch LocalGL2.Kirillov.finite_Qm LocalGL2.Kirillov.addCommGroup_additive_Qm LocalGL2.Kirillov.decidableEq_Ch LocalGL2.Kirillov.finite_additive_Qm IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion AutomorphicForm.compactSpace_maximalCompactAway

attribute [-instance] AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar

set_option autoImplicit false

p2m_open

open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion

p2m_open

open scoped nonZeroDivisors

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField Matrix

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace Ws23PencSwap

p2m_open

open scoped Pointwise

theorem modulus_det_eq_one_of_mem_localLevelOne (p : HeightOneSpectrum (𝓞 ℚ)) {N : Ideal (𝓞 ℚ)}
    {u : GL (Fin 2) (p.adicCompletion ℚ)} (hu : u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) :
    LanglandsTunnell.TateLocal.modulus
      ((Matrix.GeneralLinearGroup.det u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
  have hu' := (AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ p u).1 hu
  have h1 := Ws23Fam5Holes.det_mem_of_forall_mem _ hu'.1.integral
  have h2 := Ws23Fam5Holes.det_mem_of_forall_mem _ hu'.2.integral
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  have hprod : Matrix.det (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
      Matrix.det ((u⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hv : Valued.v (Matrix.det (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) = 1 := by
    refine le_antisymm h1 ?_
    have h := congrArg Valued.v hprod
    rw [map_mul, map_one] at h
    calc (1 : WithZero (Multiplicative ℤ)) = _ * _ := h.symm
      _ ≤ Valued.v (Matrix.det (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  rw [Matrix.GeneralLinearGroup.val_det_apply, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p,
    ← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one, NumberField.FinitePlace.norm_def, hv, map_one, NNReal.coe_one]

end Ws23PencSwap
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_gl3Translates_sum_rsFinIntegral_cells_eq_const_and_dual_eq_rootNumberMonomial_of_finWhittaker_one_ne_zero_of_localSpaceAt_of_member_of_fe32_normPin_twisted_offSQ_archPsi_bump_levelShift_global
