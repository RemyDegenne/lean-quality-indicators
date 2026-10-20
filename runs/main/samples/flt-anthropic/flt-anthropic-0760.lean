namespace P2MW.S_WeierstrassCurve_Affine_valuation_placeOf_map_of_algHom

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

open Polynomial

open scoped Polynomial.Bivariate

namespace K8T3a

section BCRing

variable {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K'] (W : WeierstrassCurve F)
  (f : K →ₐ[F] K')

theorem map_XYIdeal (x y : K) :
    (CoordinateRing.XYIdeal (W⁄K) x (C y)).map (bcHom W f) = CoordinateRing.XYIdeal (W⁄K') (f x) (C (f y)) := by
  rw [CoordinateRing.XYIdeal, Ideal.map_span, Set.image_pair, CoordinateRing.XClass,
    CoordinateRing.YClass, bcHom_mk, bcHom_mk]
  simp only [Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, coe_mapRingHom, RingHom.coe_coe]
  rfl

end BCRing
end K8T3a
end P2MW.S_WeierstrassCurve_Affine_valuation_placeOf_map_of_algHom
