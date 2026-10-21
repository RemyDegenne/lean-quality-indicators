namespace OAI

noncomputable section

open Polynomial

namespace DimensionTen.Mod41

theorem pow16_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_10 z * pow16_10 z = pow16_20_q z * f z + pow16_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_20_mul_integer z

end DimensionTen.Mod41
end
end OAI
