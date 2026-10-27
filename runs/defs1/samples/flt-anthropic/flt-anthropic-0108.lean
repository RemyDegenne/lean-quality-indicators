namespace P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field

attribute [-instance] WeierstrassCurve.Generic.isElliptic_curve WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv

set_option autoImplicit false

universe u

noncomputable section

p2m_open

namespace ModularCurve

namespace QExpSplitDevissage

p2m_open

p2m_open

open scoped TensorProduct

section Forms

variable (p : ℕ)

def vcForm (k : ℤ) : UnivBasisRing p →ₗ[ℤ] VCRing p where
  toFun t := vcBeta p t - (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) * VCRing.ofUniv p t
  map_add' x y := by simp only [map_add]; ring
  map_smul' n x := by simp only [zsmul_eq_mul, eq_intCast, Int.cast_id, map_mul, map_intCast]; ring

end Forms
end QExpSplitDevissage
end ModularCurve
end
end P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field
