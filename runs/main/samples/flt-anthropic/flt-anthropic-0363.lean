namespace P2MW.S_ModularCurve_exists_ringEquiv_adicCompletion_modularLocalizedAtPoint_uvCrossingModel_of_eq_zero_or_eq_1728

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instTopologicallyFGOfFiniteType

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

set_option autoImplicit false

p2m_open

open ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized

noncomputable section

namespace ModularCurve

p2m_open

namespace Ws30HeadGlue

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)

local notation "Qb" => AlgebraicClosure ℚ

scoped instance instCharZeroLQ' : CharZero LQ := charZero_of_injective_algebraMap (algebraMap Qb LQ).injective

section Field

variable (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ Qb)

variable {q K}

theorem coe_apply_three {x : RingAut ↥(lambdaFieldOver q K)} {b : Fin 6} {z : ↥(lambdaFieldOver q K)}
    (h : ((x z : ↥(lambdaFieldOver q K)) : LQ) = anh b (z : LQ)) :
    ((x (x (x z)) : ↥(lambdaFieldOver q K)) : LQ) = anh b (anh b (anh b (z : LQ))) := by
  have h2 := coe_apply_two h
  have hba : ((anh b (anh b z) : ↥(lambdaFieldOver q K)) : LQ) = anh b (anh b (z : LQ)) := by
    have e1 := map_anh (lambdaFieldOver q K).subtype b (anh b z)
    have e2 := map_anh (lambdaFieldOver q K).subtype b z
    simp only [Subfield.coe_subtype] at e1 e2
    rw [e1, e2]
  have : x (x z) = anh b (anh b z) := Subtype.ext (h2.trans hba.symm)
  rw [this, coe_apply_anh, coe_apply_anh, h]

end Field
end Ws30HeadGlue
end ModularCurve
end
end P2MW.S_ModularCurve_exists_ringEquiv_adicCompletion_modularLocalizedAtPoint_uvCrossingModel_of_eq_zero_or_eq_1728
