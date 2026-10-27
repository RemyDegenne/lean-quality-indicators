namespace P2MW.S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero

attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

p2m_reactivate

namespace KTORDBeta

open Polynomial

variable (p : ℕ)

noncomputable def ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

end KTORDBeta
end P2MW.S_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero
