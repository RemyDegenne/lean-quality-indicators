@[expose] public section

open scoped TrivSqZeroExt Polynomial DirectSum

namespace MvPolynomial

universe uR uι uB

variable {R : Type uR} {ι : Type uι} [CommRing R]

/-- The canonical coordinate in the `i`-th evaluation summand. -/
noncomputable def pointSquareZeroDelta (a : ι → R) (i : ι) : pointSquareZeroModule a :=
  by
    classical
    exact DirectSum.lof R[X] ι (fun i => R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a i)))
      i (Ideal.Quotient.mk _ 1)

end MvPolynomial
end
