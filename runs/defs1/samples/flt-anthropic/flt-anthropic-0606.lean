namespace P2MW.S_WeierstrassCurve_exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq

set_option autoImplicit false

open IsLocalRing Polynomial

open scoped Polynomial.Bivariate

namespace RigidificationA

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

section Rational

variable {K : Type*} [Field K] [DecidableEq K]

variable (C : VariableChange K) (X : WeierstrassCurve K)

noncomputable def theta {X X₂ : WeierstrassCurve K} (C : VariableChange K) (h : C • X = X₂) :
    X.toAffine.Point →+ X₂.toAffine.Point :=
  (WeierstrassCurve.pointAddEquivOfEq h).toAddMonoidHom.comp (vcInvHom C X)

end Rational
end RigidificationA
end P2MW.S_WeierstrassCurve_exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq
