namespace P2MW.S_ModularCurve_NodeLocalized_exists_surjective_mvPowerSeries_adicCompletion_modularLocalizedAtPoint

attribute [-instance] ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

set_option autoImplicit false

set_option linter.unusedSectionVars false

open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace PowerSeries p2m_export "PowerSeries" "coe_mul algebraMap_apply subst monomial coeff_mk mk trunc eq_X_mul_shift_add_const eval₂_X coeff_coe coeff_C coeff_one eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc constantCoeff coeff_C_mul coe_one eval₂_C coeff_mul coe_X coeff_map coe_eval₂Hom divXPowOrder order isUnit_iff_constantCoeff ext map_C map C X_pow_order_mul_divXPowOrder constantCoeff_divXPowOrder_eq_zero_iff coeff X coeff_monomial coe_C coeff_X quotient_span_X_sub_C_pow_of_irreducible" end PowerSeries

p2m_open_scoped "PowerSeries" in

namespace Submodule p2m_export "Submodule" "Quotient.eq mem_sup_right smul_mem' mk smul_mem mem_bot mem_span_singleton_self mk.injEq Quotient.mk span smul_induction_on mem_map_of_mem add_mem_sup span_le mem_comap mem_span_range_iff_exists_fun pow_mem_pow mul_le mem_top mem_span_singleton fg_iff_exists_fin_generating_family mul_mem_mul smul_mem_smul generators nontrivial_iff map_smul' zero one map_span Quotient.mk_surjective span_mono map rec Quotient.nontrivial_iff mem_sup smul_mono_left subset_span module smul_def FG ext factor_mk add factorPow map_sup fg_span mem_sup_left map_le_iff_le_comap restrictScalars_mem" end Submodule

p2m_open_scoped "Submodule" in

namespace PowerSeries

p2m_open

variable {A S : Type*} [CommRing A] [CommRing S]

theorem liftOfIsAdicCompleteAux_compat (J : Ideal S) (θ : A →+* S) (x : S) (hx : x ∈ J) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (liftOfIsAdicCompleteAux J θ x hx n) =
      liftOfIsAdicCompleteAux J θ x hx m := by
  ext F
  simp only [RingHom.comp_apply, liftOfIsAdicCompleteAux_apply, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  exact liftOfIsAdicComplete_sum_range_sub_sum_range_mem J θ x hx F hle

end PowerSeries
end Submodule
end PowerSeries
end P2MW.S_ModularCurve_NodeLocalized_exists_surjective_mvPowerSeries_adicCompletion_modularLocalizedAtPoint
