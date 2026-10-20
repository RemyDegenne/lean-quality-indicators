namespace P2MW.S_ModularCurve_finrank_adjoin_jqNModC_mul_igusaFunctionFieldX1C_eq_of_dvd

attribute [-instance] CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function ModularCurve Polynomial

open scoped Real MatrixGroups ModularForm Manifold Pointwise

namespace IgusaLevelDegDvd

section Membership

open EisensteinSeries

variable (K : Type*) [Field K]

variable (Γ : Subgroup SL(2, ℤ)) (d : ℕ) [NeZero d]

local notation "Γᴳ" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem jqNModC_eq_div : jqNModC K d = intSeriesC K (spread d pE) / intSeriesC K (spread d pD) := by
  rw [jqNModC, jqModC_eq_div, intSeriesC_spread, intSeriesC_spread, map_div₀]

end Membership
end IgusaLevelDegDvd
end
end P2MW.S_ModularCurve_finrank_adjoin_jqNModC_mul_igusaFunctionFieldX1C_eq_of_dvd
