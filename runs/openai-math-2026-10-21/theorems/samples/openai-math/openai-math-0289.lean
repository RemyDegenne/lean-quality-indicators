namespace OAI

noncomputable section

open Polynomial

namespace DimensionTen.Mod41

theorem pow14_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_20 z * pow14_20 z = pow14_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_40_mul z

end DimensionTen.Mod41
end
end OAI
