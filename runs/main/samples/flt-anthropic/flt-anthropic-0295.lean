namespace P2MW.S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist

attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine

attribute [-instance] ModularCurve.unimodularRowSetoid

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve AlgebraicCurve Polynomial

namespace WNormSwapSol

local notation "Qb" => AlgebraicClosure ℚ

scoped instance (priority := low) neZero_of_fact_prime {p : ℕ} [hp : Fact p.Prime] : NeZero p :=
  ⟨hp.out.ne_zero⟩

section Square

variable {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

attribute [local instance] algIncl

variable (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  {θ : FH M H ≃ₐ[Qb] FH M H} (hθ : Pin (p := p) (hpM := hpM) θ)
  {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ p)
  (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) =
    (p : ZMod (M / p)))
  (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ infSubgroup p M H hpM ∨
    -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ infSubgroup p M H hpM)

include hpM2 hHp hθ hζ hd hdH in

theorem θ_θ_γel : θ (θ (γel θ)) = γel θ := by

  have hψ : ((ψinf p).comp (θ.trans θ : FH M H →+* FH M H)).comp
      (incl p M H hpM : FH' p M H hpM →+* FH M H) = e0 p M H hpM := by
    refine RingHom.ext fun u => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, e0_apply, ψinf_apply, AlgHom.coe_toRingHom]
    change qExpand Qb p (((θ.trans θ) (incl p M H hpM u) : FH M H) : LaurentSeries Qb) = _
    rw [AlgEquiv.trans_apply, θ_θ_incl hpM2 hHp hθ d hd hdH, coe_incl]
  have hroot := isRoot_map_μ (hpM := hpM) θ hψ
  rw [(map_μ_eq hpM2 hHp hθ hζ).1, PiPoly, IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hroot
  obtain ⟨o, -, ho⟩ := hroot
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at ho
  change qExpand Qb p ((θ (θ (γel θ)) : FH M H) : LaurentSeries Qb) = sv p θ ζ o at ho
  rcases o with _ | b
  · rw [sv_none] at ho
    exact Subtype.ext (qExpand_injective p ho)
  ·
    have h1 := congrArg (fun s : LaurentSeries Qb => s.coeff 1) ho
    rw [qExpand_coeff_one, sv_some_coeff_one] at h1
    exact absurd h1.symm (mul_ne_zero (pow_ne_zero _ (Units.ne_zero ζ)) (by norm_num))

end Square
end WNormSwapSol
end
end P2MW.S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist
