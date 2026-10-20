namespace P2MW.S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

set_option autoImplicit false

set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing

namespace ChartOkAbv

set_option autoImplicit false

variable {L : Type*} [Field L] (A : ValuationSubring L) (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)

include hμA

theorem abv_lt_one_iff_mem_maximalIdeal {a : L} (haA : a ∈ A) (ha : a ≠ 0) :
    μ a < 1 ↔ (⟨a, haA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  rw [abv_lt_one_iff_inv_not_mem A μ hμA ha, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h hu
    apply h
    have hmul : ((hu.unit⁻¹ : Aˣ) : A).1 * a = 1 := by
      have h' := congrArg Subtype.val hu.unit.inv_mul
      rw [IsUnit.unit_spec] at h'
      exact h'
    have : ((hu.unit⁻¹ : Aˣ) : A).1 = a⁻¹ := eq_inv_of_mul_eq_one_left hmul
    rw [← this]; exact Subtype.mem _
  · intro h hinv
    exact h ⟨⟨⟨a, haA⟩, ⟨a⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha), Subtype.ext (inv_mul_cancel₀ ha)⟩, rfl⟩

end ChartOkAbv
end P2MW.S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist
