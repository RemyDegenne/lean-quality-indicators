namespace P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_isIntegralQExp_gamma1

attribute [-instance] CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex WeierstrassCurve.Affine.Point.instFinite TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups ModularForm

p2m_reactivate

p2m_reactivate

namespace ChartMemAsm

open ModularForm UpperHalfPlane ModularCurve Polynomial CongruenceSubgroup SlashInvariantForm ChartMemNorm

section Setup

variable (M : ℕ) [NeZero M] (k : ℕ)

noncomputable def deltaPow : ModularForm 𝒮ℒ (12 * (k : ℤ)) :=
  ((ModularFormClass.modularForm (CuspForm.discriminant)).pow k).mcast (by ring)

end Setup
end ChartMemAsm
end
end P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_isIntegralQExp_gamma1
