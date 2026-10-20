namespace P2MW.S_WeierstrassCurve_Affine_weilPairing0_galois

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

p2m_open

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

namespace Affine

p2m_open

section GalA

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] (W : WeierstrassCurve F)
  (σ : K ≃ₐ[F] K) (Φ : (W⁄K).FunctionField →+* (W⁄K).FunctionField)
  (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
    algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField
      (CoordinateRing.mk (W⁄K) (p.map (mapRingHom (σ : K →+* K)))))

include hΦ

theorem map_galAlgHom_baseChange (S : (W⁄K).Point) :
    Point.map (galAlgHom W σ Φ hΦ) (Point.baseChange K (W⁄K).FunctionField S) =
      Point.baseChange K (W⁄K).FunctionField (σ • S) := by
  rcases S with _ | ⟨x, y, hxy⟩
  · rfl
  · rw [Point.algEquiv_smul_def, Point.map_some, Point.baseChange, Point.map_some, Point.map_some,
      Point.map_some]
    congr 1
    · exact gal_algebraMap W σ Φ hΦ x
    · exact gal_algebraMap W σ Φ hΦ y

end GalA
end Affine
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_Affine_weilPairing0_galois
