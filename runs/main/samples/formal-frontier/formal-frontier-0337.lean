@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace SpecialLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

theorem quotient_det :
    quotient K n (matrix K n).det = 1 := by
  have hz : quotient K n ((matrix K n).det - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  simpa only [map_sub, map_one, sub_eq_zero] using hz

end SpecialLinearCoordinateRing
end
end
