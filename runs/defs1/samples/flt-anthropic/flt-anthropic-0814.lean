namespace P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X

attribute [-instance] AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option autoImplicit false

set_option maxHeartbeats 3200000

open Polynomial

namespace AlgebraicCurve

p2m_open

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

set_option autoImplicit false

noncomputable section

p2m_open

namespace AlgebraicCurve

p2m_open

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def lSpaceShiftEquiv (D : Divisor K F) {g : F} (hg : g ≠ 0)
    {Dg : Divisor K F} (hDg : ∀ v, Dg v = v.ord g) :
    LSpace D ≃ₗ[K] LSpace (D + Dg) where
  toFun h := ⟨(h : F) * g⁻¹, by
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (h : F) 0 with hh0 | hh0
    · left; rw [hh0, zero_mul]
    · right; intro v
      rw [Finsupp.add_apply, hDg, v.ord_mul hh0 (inv_ne_zero hg), v.ord_inv]
      have := (mem_lSpace_iff_ord.mp h.2).resolve_left hh0 v
      linarith⟩
  invFun k := ⟨(k : F) * g, by
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (k : F) 0 with hk0 | hk0
    · left; rw [hk0, zero_mul]
    · right; intro v
      have := (mem_lSpace_iff_ord.mp k.2).resolve_left hk0 v
      rw [Finsupp.add_apply, hDg] at this
      rw [v.ord_mul hk0 hg]
      linarith⟩
  map_add' h₁ h₂ := by apply Subtype.ext; push_cast; ring
  map_smul' c h := by
    apply Subtype.ext
    simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
    ring
  left_inv h := by
    apply Subtype.ext
    show (h : F) * g⁻¹ * g = (h : F)
    rw [mul_assoc, inv_mul_cancel₀ hg, mul_one]
  right_inv k := by
    apply Subtype.ext
    show (k : F) * g * g⁻¹ = (k : F)
    rw [mul_assoc, mul_inv_cancel₀ hg, mul_one]

end AlgebraicCurve
end
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X
