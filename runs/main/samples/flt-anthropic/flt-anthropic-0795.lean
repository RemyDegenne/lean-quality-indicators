namespace P2MW.S_AlgebraicCurve_TranscendenceTower_poleDivisor_apply

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy

set_option autoImplicit false

set_option maxHeartbeats 3200000

namespace AlgebraicCurve

p2m_open

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve

p2m_open

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace RiemannGenusReachedAt p2m_export "AlgebraicCurve.RiemannGenusReachedAt" "finite mk eq isMax" end RiemannGenusReachedAt

theorem gate_indexOfSpecialty_at_witness [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    (indexOfSpecialty D₀ : ℤ) = 0 := by
  have h1 := (indexOfSpecialty_eq_of_genusReached h D₀).2
  have h2 := h.eq
  have h3 := indexOfSpecialty_eq_zero_of_genusReached h
  exact_mod_cast h3

end RiemannGenusReachedAt
end AlgebraicCurve
end
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_TranscendenceTower_poleDivisor_apply
