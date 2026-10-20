namespace P2MW.S_ModularCurve_PlaceSpecialization_gluedSpecialization_nodeUnit_heckeGen_eq_nodePerm_symm_comp

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral

set_option autoImplicit false

set_option Elab.async false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace UqNSol

open scoped Pointwise

open AlgebraicCurve ModularCurve IsLocalRing

section Values

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def resHom (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong ψ hψ).toValuationSubring →+* w.toValuationSubring where
  toFun x := ⟨ψ x, x.2⟩
  map_one' := Subtype.ext (map_one ψ)
  map_mul' x y := Subtype.ext (map_mul ψ _ _)
  map_zero' := Subtype.ext (map_zero ψ)
  map_add' x y := Subtype.ext (map_add ψ _ _)

end Values
end UqNSol
end P2MW.S_ModularCurve_PlaceSpecialization_gluedSpecialization_nodeUnit_heckeGen_eq_nodePerm_symm_comp
