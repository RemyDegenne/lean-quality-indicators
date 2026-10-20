namespace P2MW.S_ModularCurve_IsGamma1Link_of_map_of_surjective_of_ker_pow_eq_bot

attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve

set_option autoImplicit false

set_option linter.unusedVariables false

universe u

open Polynomial

namespace LinkLift

theorem hom_eval {R S : Type u} [CommRing R] [CommRing S] (χ : R →+* S) (p : R[X]) (a : R) :
    χ (p.eval a) = (p.map χ).eval (χ a) := by
  rw [eval_map, eval₂_at_apply]

end LinkLift
end P2MW.S_ModularCurve_IsGamma1Link_of_map_of_surjective_of_ker_pow_eq_bot
