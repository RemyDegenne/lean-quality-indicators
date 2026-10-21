namespace OAI

noncomputable section

open Polynomial

namespace DimensionTen.Mod41

theorem pow19_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_40 z * u18 z = pow19_41_q z * f z + pow19_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_41_mul_integer z

end DimensionTen.Mod41
end
end OAI
