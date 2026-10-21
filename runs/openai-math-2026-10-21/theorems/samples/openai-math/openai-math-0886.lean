namespace OAI

noncomputable section

open Polynomial

namespace DimensionTen.Mod41

theorem pow15_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_40 z * u14 z = pow15_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_41_mul z

end DimensionTen.Mod41
end
end OAI
