@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x

namespace GeneralLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type v) [Fintype n] [DecidableEq n]

@[simp] theorem matrix_apply (i j : n) :
    matrix K n i j = algebraMap (PolynomialRing K n) (CoordinateRing K n)
      (MvPolynomial.X (i, j)) := rfl

end GeneralLinearCoordinateRing
end
end
