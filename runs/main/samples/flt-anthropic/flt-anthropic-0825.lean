namespace P2MW.S_ModularCurve_exists_coe_eq_div_pow_and_mul_min_ord_le_ord_x1FunctionFieldC

attribute [-instance] CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex WeierstrassCurve.Affine.Point.instFinite TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularCurve AlgebraicCurve Polynomial

open scoped MatrixGroups ModularForm

namespace RegKBody

section IntModels

variable (K : Type*) [Field K]

theorem laurentMap_ofPowerSeries_int (q : PowerSeries ℤ) :
    laurentMap (Int.castRingHom K) (HahnSeries.ofPowerSeries ℤ ℤ q) = intSeriesC K q := by
  rw [laurentMap_ofPowerSeries]; rfl

end IntModels
end RegKBody
end
end P2MW.S_ModularCurve_exists_coe_eq_div_pow_and_mul_min_ord_le_ord_x1FunctionFieldC
