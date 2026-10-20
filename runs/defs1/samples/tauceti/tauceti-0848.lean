public section

open Polynomial LaurentSeries HahnSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The **Laurent expansion at the point at infinity** of a function on the affine Weierstrass
curve: the `R`-algebra homomorphism `R[W] →ₐ[R] R⸨X⸩` sending `x` to `z⁻² u(z)⁻¹ = z / w(z)` and
`y` to `-z⁻³ u(z)⁻¹ = -1 / w(z)`, where `z` is the variable of the Laurent series ring and
`w(z) = z³ u(z)` is the `w`-expansion `WeierstrassCurve.formalW` of `W`. -/
noncomputable def laurentExpansion : W.toAffine.CoordinateRing →ₐ[R] R⸨X⸩ :=
  Affine.CoordinateRing.evalAlgHom W.equation_laurent

end WeierstrassCurve
end
