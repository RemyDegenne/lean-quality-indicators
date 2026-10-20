@[expose] public section

namespace PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

variable {A}

theorem derivative_log_mul_one_add_X : d⁄dX (log A) * (1 + X) = 1 := by
  rw [derivative_log, mk_neg_one_pow_mul_one_add_eq_one]

end PowerSeries
end
