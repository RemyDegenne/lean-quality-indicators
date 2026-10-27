namespace P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq

attribute [-instance] WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 3200000

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

scoped instance instFactNatPrime2_s13s2c : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

scoped instance instFactNatPrime3_s13s2c : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

namespace WeierstrassCurve

namespace Affine

p2m_open

p2m_open

p2m_open_scoped

variable {F : Type*} [Field F] {W : Affine F}

p2m_reactivate

p2m_open

def IsFinitePlace (v : AlgebraicCurve.Place F W.FunctionField) : Prop :=
  ∀ r : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField r ∈ v.toValuationSubring

end Affine
end WeierstrassCurve
end
end P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq
