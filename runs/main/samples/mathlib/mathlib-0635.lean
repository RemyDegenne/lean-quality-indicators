public section

open Set

variable {F R S : Type*}

namespace Int

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

section fract

variable [IsOrderedAddMonoid R]

@[simp]
theorem fract_sub_intCast (a : R) (m : ℤ) : fract (a - m) = fract a := by
  rw [fract]
  simp

end fract
end Int
end
