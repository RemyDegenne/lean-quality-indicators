@[expose] public section

noncomputable section

universe u v s t

namespace SplitQuadric

variable (A : Type u) [CommRing A]

/-- The determinant of the matrix with rows `(w, x)` and `(y, z)`. -/
def relation : Polynomial A :=
  MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2

end SplitQuadric
end
end
