namespace P2MW.S_ModularCurve_stackOrd_nonneg_and_le_ord_of_isModPFormFn

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 80000

open AlgebraicCurve ModularCurve

noncomputable section

namespace DictDiv

section Main

variable (p : ℕ) [hp : Fact p.Prime] (N : ℕ) [NeZero N]
  (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (m : ℕ)

theorem isIntegral_X (G : ↥(modularFunctionFieldC K N)) (hG : IsModPFormFn K m (G : LaurentSeries K)) :
    IsIntegral (Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)))
      (G ^ 6 * jGeomGen K N ^ (4 * m) * (jGeomGen K N - algebraMap K _ 1728) ^ (3 * m)) := by
  apply isIntegral_adjoin_of_coe
  have hcoe : ((G ^ 6 * jGeomGen K N ^ (4 * m) * (jGeomGen K N - algebraMap K _ 1728) ^ (3 * m) :
      ↥(modularFunctionFieldC K N)) : LaurentSeries K)
      = (G : LaurentSeries K) ^ 6 * jqModC K ^ (4 * m) * (jqModC K - algebraMap K (LaurentSeries K) 1728) ^ (3 * m) := by
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_pow, IntermediateField.coe_pow,
      IntermediateField.coe_pow, AddSubgroupClass.coe_sub, coe_jGeomGen]
    rfl
  rw [coe_jGeomGen, hcoe]
  exact hG.1

end Main
end DictDiv
end
end P2MW.S_ModularCurve_stackOrd_nonneg_and_le_ord_of_isModPFormFn
