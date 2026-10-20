@[expose] public section

open scoped TrivSqZeroExt Polynomial DirectSum

namespace MvPolynomial

universe uR uι uB

variable {R : Type uR} {ι : Type uι} [CommRing R]

/-- The direct sum of polynomial modules of point evaluations. -/
abbrev pointSquareZeroModule (a : ι → R) : Type _ :=
  ⨁ i : ι, (R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a i)))

end MvPolynomial
end
