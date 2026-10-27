namespace P2MW.S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_three

attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation

attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option synthInstance.maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve AlgebraicCurve

open scoped MatrixGroups

noncomputable section

namespace P2MKcCEN3H

section Level

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

variable (H)

scoped instance actXV : MulAction SL(2, ℤ) (XH (V M) M H) where
  smul g s := mapX (ractHom M g⁻¹) (ractHom_injective g⁻¹) s
  one_smul s := mapX_id' _ (fun v => by simp [ract_one]) s
  mul_smul g h s := by
    show mapX (ractHom M (g * h)⁻¹) _ s = mapX (ractHom M g⁻¹) _ (mapX (ractHom M h⁻¹) _ s)
    rw [mapX_mapX]
    exact mapX_congr _ _ (by rw [ractHom_comp, mul_inv_rev]) s

variable {H}

section CycAct

variable {X : Type*} [MulAction SL(2, ℤ) X] (p : ℕ) [hp : Fact p.Prime] (g₀ : SL(2, ℤ))
  (htriv : ∀ s : X, (g₀ ^ p) • s = s)

@[reducible] def cycAct : MulAction (Multiplicative (ZMod p)) X := MulAction.compHom X (cycHom p g₀ htriv)

end CycAct
end Level
end P2MKcCEN3H
end
end P2MW.S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_three
