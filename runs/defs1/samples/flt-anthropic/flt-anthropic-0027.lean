namespace P2MW.S_ModularCurve_exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot

attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

set_option linter.unusedSectionVars false

open ModularCurve WeierstrassCurve

universe u

namespace TateTransfer

namespace Arith

open CyclotomicUniv

section Consts

variable (N : ℕ) {ℓ : ℕ} (h : ℓ ∣ N)

noncomputable def sB (ℓ : ℕ) : base N := (((ℓ - 1) / 2 : ℕ) : base N)

end Consts
end Arith
end TateTransfer
end P2MW.S_ModularCurve_exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot
