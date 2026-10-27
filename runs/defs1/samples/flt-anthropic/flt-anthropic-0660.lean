namespace P2MW.S_WeierstrassCurve_Affine_exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add

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

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

section

section

p2m_open

p2m_open_scoped

noncomputable section

namespace WeierstrassCurve

namespace Affine

p2m_open

p2m_open

universe u

variable {F : Type u} [Field F]

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section TranslationHom

variable {W : Affine F} {a b : F} (hA : W.Equation a b)

variable (htr : AddXFunTranscendental W a b)

def translationHom : W.FunctionField →ₐ[F] W.FunctionField :=
  IsFractionRing.liftAlgHom (translationCoordHom_injective hA htr)

end TranslationHom
end Affine
end WeierstrassCurve
end
end
end
end
end
end
end
end
end P2MW.S_WeierstrassCurve_Affine_exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add
