namespace P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom

set_option autoImplicit false

p2m_open

open Polynomial

open scoped Polynomial.Bivariate

p2m_reactivate

p2m_reactivate

p2m_reactivate

theorem solution
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K'] [DecidableEq K] [DecidableEq K']
    [IsAlgClosed K] [IsAlgClosed K'] (W : WeierstrassCurve F) [W.IsElliptic] (f : K →ₐ[F] K')
    (Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField)
    (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
      algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))))
    (S : (W⁄K).Point) (h : (W⁄K).FunctionField) :
    Φ (transEquiv W K S h) = transEquiv W K' (WeierstrassCurve.Affine.Point.map f S) (Φ h) :=
  WeierstrassCurve.Affine.TransEquivBaseChangeAux.main W f Φ hΦ S h

end P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom
