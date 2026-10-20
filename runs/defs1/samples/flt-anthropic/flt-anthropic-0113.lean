namespace P2MW.S_ModularCurve_XOneGammaZeroP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1x0_gamma0

attribute [-instance] WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_open

open scoped MatrixGroups ModularForm

namespace INVOL

variable {N : Subgroup SL(2, ℤ)} [hTN : Fact (ModularGroup.T ∈ N)]

section Ratio

variable {p : ℕ} {γ : SL(2, ℤ)} {Lc : Subfield ℂ}

structure WData (p : ℕ) (γ : SL(2, ℤ)) (Lc : Subfield ℂ) {k : ℤ} (f : MF N k) where
  D : ℤ
  hD : D ≠ 0
  φ : MF N k
  hφ : φ ∈ LForms Lc k
  eq : (⇑φ : ℍ → ℂ) = (D : ℂ) • Wfun p γ k ⇑f

end Ratio
end INVOL
end
end P2MW.S_ModularCurve_XOneGammaZeroP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1x0_gamma0
