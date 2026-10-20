public section

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R]

theorem mk_dickson_two_eval_mul_one_sub_add_eq_one (t a : R) :
    (PowerSeries.mk fun n ↦ (dickson 2 a n).eval t) *
      (1 - PowerSeries.C t * PowerSeries.X + PowerSeries.C a * PowerSeries.X ^ 2) = 1 := by
  simp only [mul_comm (PowerSeries.mk _), add_mul, sub_mul, one_mul, sq, mul_assoc]
  -- compare coefficients; at `X ^ (n + 2)` this is the recurrence `dickson_add_two`
  ext (_ | _ | n) <;> norm_num

end Polynomial
end
