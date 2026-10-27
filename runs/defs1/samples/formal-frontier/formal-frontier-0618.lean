@[expose] public section

universe u v w z

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

/-- The matrix with first component the identity and second component `X`. -/
def liftMatrix (X : Matrix n n R) : Matrix n n (DualNumber R) :=
  fun i j => ((1 : Matrix n n R) i j, X i j)

end Matrix.DualNumberKernels
end
