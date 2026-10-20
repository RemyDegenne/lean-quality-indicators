namespace P2MW.S_ModularCurve_cuspChartInftyZero_place_unique

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

open AlgebraicCurve ModularCurve

set_option autoImplicit false

set_option Elab.async false

open AlgebraicCurve ModularCurve IntermediateField Polynomial

noncomputable section

namespace S09CDT

section Counting

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem place_eq_of_vanishing_chart {p : ℕ} (hp : 2 ≤ p) (hfin : Module.finrank F F' ≤ p + 1)
    {jF : F} (hpole : ∀ v v' : Place K F, v.ord jF < 0 → v'.ord jF < 0 → v = v')
    (hpole1 : ∀ v : Place K F, v.ord jF < 0 → v.ord jF = -1)
    (Φ : Polynomial (Polynomial ℤ))
    (hΦ₁ : ∀ b a : ℕ, ((Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 → 1 * a + p * b ≤ p ^ 2 + p - 1)
    (hΦ₂ : ∀ b a : ℕ, ((Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 → p * a + 1 * b ≤ p ^ 2 + p - 1)
    {y : F'} (hrel : Φ.eval₂ (eval₂RingHom (Int.castRingHom F') (algebraMap F F' (jF⁻¹)⁻¹)) y = 0)
    {U U' : Place K F'}
    (hUj : U.ord (algebraMap F F' jF) < 0) (hUt : 0 < U.ord (y * algebraMap F F' (jF⁻¹ ^ p)))
    (hU'j : U'.ord (algebraMap F F' jF) < 0) (hU't : 0 < U'.ord (y * algebraMap F F' (jF⁻¹ ^ p))) : U = U' := by
  have hj0 : jF ≠ 0 := by
    rintro rfl
    rw [map_zero, Place.ord_zero] at hUj
    exact lt_irrefl _ hUj
  have hjF' : algebraMap F F' jF ≠ 0 := (_root_.map_ne_zero _).mpr hj0
  rw [inv_inv] at hrel
  have key : ∀ W : Place K F', W.ord (algebraMap F F' jF) < 0 → 0 < W.ord (y * algebraMap F F' (jF⁻¹ ^ p)) →
      (W.restrict F).ord jF < 0 ∧ p ≤ W.ramificationIndex F := by
    intro W hWj hWt
    obtain ⟨hWy, hdich⟩ := Place.ord_eq_mul_or_eq_mul_of_modular_support W (by omega) Φ hΦ₁ hΦ₂ hrel hWj
    have hy0 : y ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hWy; exact lt_irrefl _ hWy

    have ht : W.ord (y * algebraMap F F' (jF⁻¹ ^ p)) = W.ord y - p * W.ord (algebraMap F F' jF) := by
      rw [map_pow, map_inv₀, W.ord_mul hy0 (pow_ne_zero _ (inv_ne_zero hjF')), ord_pow W (inv_ne_zero hjF'),
        Place.ord_inv]
      ring
    rw [ht] at hWt
    rcases hdich with hxy | hyx
    ·
      have hres := Place.ord_restrict (F := F) W jF
      have hvneg : (W.restrict F).ord jF < 0 := by
        by_contra hcon
        have : (0 : ℤ) ≤ (W.ramificationIndex F : ℤ) * (W.restrict F).ord jF := mul_nonneg (by positivity) (not_lt.mp hcon)
        omega
      refine ⟨hvneg, ?_⟩
      rw [hpole1 _ hvneg] at hres
      have : (p : ℤ) ≤ W.ramificationIndex F := by nlinarith
      exact_mod_cast this
    ·
      exfalso
      rw [hyx] at hWt
      simp at hWt
  obtain ⟨hUv, hUe⟩ := key U hUj hUt
  obtain ⟨hU'v, hU'e⟩ := key U' hU'j hU't
  exact Place.eq_of_finrank_lt_two_mul_ramificationIndex (hpole _ _ hU'v hUv) (by omega) hUe hU'e

end Counting
end S09CDT
end
end P2MW.S_ModularCurve_cuspChartInftyZero_place_unique
