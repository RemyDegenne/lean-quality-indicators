namespace P2MW.S_ModularCurve_FullLevel_Diamond_zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

open scoped Classical

open ModularCurve ModularCurve.LevelRelabelling

namespace H34A

theorem pmap_some {K F : Type} [Field K] [Field F] [Algebra K F] (W : WeierstrassCurve K) {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    pmap (F := F) W (WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some (algebraMap K F x) (algebraMap K F y)
        ((WeierstrassCurve.Affine.map_nonsingular W (algebraMap K F).injective x y).mpr h) := rfl

end H34A
end P2MW.S_ModularCurve_FullLevel_Diamond_zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow
