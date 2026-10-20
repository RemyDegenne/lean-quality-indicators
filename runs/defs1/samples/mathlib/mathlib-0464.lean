@[expose] public section

open FractionalIdeal (coeIdeal_mul)

open Ideal hiding map_mul

open Module Polynomial

open scoped nonZeroDivisors Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

universe r s u v w

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} {L : Type w} [CommRing R]
  [CommRing S] [CommRing A] [CommRing B] [Field F] [Field K] [Field L] {W' : Affine R}
  {W : Affine F}

namespace Affine

section IsElliptic

variable [Nontrivial R] [W'.IsElliptic]

/-- A point on an elliptic curve `W` over `R`. -/
def Point.mk {x y : R} (h : W'.Equation x y) : W'.Point :=
  .some _ _ <| equation_iff_nonsingular.mp h

end IsElliptic
end Affine
end WeierstrassCurve
end
