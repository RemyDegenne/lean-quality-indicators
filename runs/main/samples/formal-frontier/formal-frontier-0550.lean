@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x

namespace GeneralLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type v) [Fintype n] [DecidableEq n]

variable {K n}

variable (K n)

@[simp] theorem counit_detInverse : counit K n (detInverse K n) = 1 := by
  rw [counit, evaluate_detInverse]
  simp

end GeneralLinearCoordinateRing
end
end
