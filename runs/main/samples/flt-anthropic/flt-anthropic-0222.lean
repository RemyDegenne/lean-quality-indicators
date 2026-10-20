namespace P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index

attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

attribute [-instance] DivisionRing.toRatAlgebra

namespace FIdxLevelOne

open ModularForm UpperHalfPlane EisensteinSeries

open scoped MatrixGroups

theorem qExpansion_mem_monomialSpan (m : ℕ) :
    ∀ (k : ℤ) (hk : k = 12 * (m : ℤ)) (h : ModularForm 𝒮ℒ k), qExpansion 1 (h : ℍ → ℂ) ∈ monomialSpan m := by
  induction m with
  | zero =>
    intro k hk h
    simp only [Nat.cast_zero, mul_zero] at hk
    subst hk
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const h
    have hh : h = c • (1 : ModularForm 𝒮ℒ 0) := by
      ext z
      rw [hc, IsGLPos.smul_apply]
      simp
    rw [hh, IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_one]
    refine Submodule.smul_mem _ _ ?_
    have := monomial_mem 0 0 le_rfl
    simpa using this
  | succ m ih =>
    intro k hk h
    set a₀ : ℂ := PowerSeries.coeff 0 (qExpansion 1 (h : ℍ → ℂ)) with ha₀
    let P : ModularForm 𝒮ℒ k := (E₄.pow (3 * (m + 1))).mcast (by rw [hk]; push_cast; ring)
    have hP : qExpansion 1 (P : ℍ → ℂ) = q4 ^ (3 * (m + 1)) := by
      simp only [P, ModularForm.qExpansion_mcast,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    let g : ModularForm 𝒮ℒ k := h - a₀ • P
    have hg : qExpansion 1 (g : ℍ → ℂ) = qExpansion 1 (h : ℍ → ℂ) - a₀ • q4 ^ (3 * (m + 1)) := by
      simp only [g]
      rw [coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, IsGLPos.coe_smul,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hP]
    have hg0 : PowerSeries.coeff 0 (qExpansion 1 (g : ℍ → ℂ)) = 0 := by
      have h4 : PowerSeries.coeff 0 (q4 ^ (3 * (m + 1))) = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, q4_coeff_zero, one_pow]
      rw [hg, map_sub, map_smul, h4, smul_eq_mul, mul_one, ha₀, sub_self]

    have hΔ := ModularForm.qExpansion_eq_qExpansion_discriminant_mul g hg0
    have hk' : k - 12 = 12 * (m : ℤ) := by rw [hk]; push_cast; ring
    have hIH := ih (k - 12) hk' (CuspForm.discriminantEquiv (g.toCuspForm hg0))

    have hh : qExpansion 1 (h : ℍ → ℂ) =
        a₀ • q4 ^ (3 * (m + 1)) +
          qΔ * qExpansion 1 (CuspForm.discriminantEquiv (g.toCuspForm hg0) : ℍ → ℂ) := by
      rw [← hΔ, hg]; abel
    rw [hh]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) ?_
    · have := monomial_mem (m + 1) 0 (Nat.zero_le _)
      simpa using this
    ·
      refine Submodule.span_induction (p := fun x _ => qΔ * x ∈ monomialSpan (m + 1))
        ?_ ?_ ?_ ?_ hIH
      · rintro _ ⟨b, rfl⟩
        have hb : (b : ℕ) ≤ m := Nat.lt_succ_iff.mp b.2
        have := monomial_mem (m + 1) (b + 1) (Nat.succ_le_succ hb)
        rw [show 3 * (m + 1 - ((b : ℕ) + 1)) = 3 * (m - b) by omega, pow_succ] at this
        rw [show qΔ * (q4 ^ (3 * (m - ↑b)) * qΔ ^ (b : ℕ)) =
          q4 ^ (3 * (m - ↑b)) * (qΔ ^ (b : ℕ) * qΔ) by ring]
        exact this
      · simp
      · intro x y _ _ hx hy
        rw [mul_add]
        exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ _ hx

end FIdxLevelOne
end P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
