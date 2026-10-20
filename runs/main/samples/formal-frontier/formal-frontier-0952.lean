@[expose] public section

open scoped TrivSqZeroExt Polynomial DirectSum

namespace MvPolynomial

universe uR uι uB

variable {R : Type uR} {ι : Type uι} [CommRing R]

@[simp] theorem pointSquareZeroLift_mk_some (a : ι → R)
    {B : Type uB} [CommRing B] [Algebra R[X] B]
    (b : ι → B) (hsq : ∀ i, b i ^ 2 = 0)
    (hlinear : ∀ i, algebraMap R[X] B (Polynomial.X - Polynomial.C (a i)) * b i = 0)
    (i : ι) :
    pointSquareZeroLift a b hsq hlinear
        (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i))) = b i := by
  simp [pointSquareZeroLift]

end MvPolynomial
end
