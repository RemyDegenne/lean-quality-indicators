@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x

namespace GeneralLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type v) [Fintype n] [DecidableEq n]

variable {K n}

@[simp] theorem toGL_apply {R : Type w} [CommRing R] [Algebra K R]
    (f : CoordinateRing K n →ₐ[K] R) (i j : n) :
    toGL f i j = f (matrix K n i j) := rfl

end GeneralLinearCoordinateRing
end
end
