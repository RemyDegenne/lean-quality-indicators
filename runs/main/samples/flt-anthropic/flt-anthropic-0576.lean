namespace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq

attribute [-instance] WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 3200000

noncomputable section

scoped instance instFactNatPrime2_s13e2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

scoped instance instFactNatPrime3_s13e2 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

scoped instance instFactNatPrime7_s13e2 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

namespace WeierstrassCurve

namespace Affine

p2m_open

p2m_open

p2m_open_scoped

variable {F : Type*} [Field F] {W : Affine F}

p2m_reactivate

p2m_open

p2m_reactivate

variable [IsDedekindDomain W.CoordinateRing]

theorem isFinitePlace_placeOfEquation {x y : F} (h : W.Equation x y) :
    IsFinitePlace (placeOfEquation h) := fun r =>
  (heightOneSpectrumOfEquation h).valuation_le_one r

end Affine
end WeierstrassCurve
end
end P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq
