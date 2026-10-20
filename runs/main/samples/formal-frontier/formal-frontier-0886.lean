@[expose] public section

open scoped TrivSqZeroExt Polynomial DirectSum

namespace MvPolynomial

universe uR uι uB

variable {R : Type uR} {ι : Type uι} [CommRing R]

@[simp] theorem pointSquareZeroForward_mk_none (a : ι → R) :
    pointSquareZeroForward a (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X none)) =
      TrivSqZeroExt.inl (Polynomial.X : R[X]) := by
  rw [pointSquareZeroForward, pointSquareZeroLift_mk_none,
    TrivSqZeroExt.algebraMap_eq_inl]

end MvPolynomial
end
