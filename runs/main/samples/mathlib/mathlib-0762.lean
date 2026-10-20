public section

open scoped nonZeroDivisors

section Monoid

variable {R : Type*} [Monoid R] {r : R}

variable [Finite R]

theorem isRegular_iff_isUnit_of_finite : IsRegular r ↔ IsUnit r where
  mp h := h.1.isUnit_of_finite
  mpr h := h.isRegular

end Monoid
end
