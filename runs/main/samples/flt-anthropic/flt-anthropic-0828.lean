namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit

attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

p2m_open

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.unusedVariables false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra ModularCurve.LevelRelabelling HomogeneousLocalization

open scoped Classical

noncomputable section

namespace WeierstrassCurve

namespace DrinfeldGlobal

namespace DrinfeldThrough

p2m_open

section General

variable {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}

theorem bc_val (S : Section W) : (bc S).1 = S.1 := by
  show σT T ≫ S.1 = S.1
  rw [σT_eq_id, Category.id_comp]

end General
end DrinfeldThrough
end DrinfeldGlobal
end WeierstrassCurve
end
end P2MW.S_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit
