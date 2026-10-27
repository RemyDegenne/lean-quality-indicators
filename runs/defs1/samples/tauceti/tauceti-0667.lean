public section

open Matrix LaurentPolynomial

namespace TauCeti.KnotTheory

variable {R : Type*} [CommRing R] {ι : Type*}

variable [Fintype ι] [DecidableEq ι]

/-- The Seifert matrix of the right-handed trefoil, read off the standard genus-one Seifert
surface (Lickorish, *An Introduction to Knot Theory*, Chapter 6). -/
def trefoilSeifertMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; 0, -1]

end TauCeti.KnotTheory
end
