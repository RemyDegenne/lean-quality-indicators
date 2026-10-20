namespace P2MW.S_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two

attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MKcNS

section Action

variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K]

theorem xy_vcInvFun (γ : VariableChange K) {W : WeierstrassCurve K} (P : W.toAffine.Point) :
    xy (Point.vcInvFun γ W.toAffine P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

end Action
end P2MKcNS
end P2MW.S_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two
