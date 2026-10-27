public section

noncomputable section

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

namespace Universal

open Coeff

/-- The universal ring for **pointed** Weierstrass curves: `ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩`, for `P` the
Weierstrass polynomial. A Weierstrass curve over `R` together with an affine point on it determines
a ring homomorphism out of it — `ringEval` — and determines it uniquely, since the coefficients and
the two coordinates generate (Mathlib's `AdjoinRoot.ringHom_ext`, through which `ext` reduces to
them). Being an `abbrev` for `curve.CoordinateRing`, it inherits Mathlib's `Affine.CoordinateRing`
API. -/
protected abbrev Ring : Type := curve.CoordinateRing

end Universal
end WeierstrassCurve
end
end
