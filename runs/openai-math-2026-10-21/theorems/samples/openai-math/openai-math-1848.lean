namespace OAI

noncomputable section

open Polynomial

namespace DimensionTen.Mod139

theorem pow15_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_69 z * pow15_69 z = pow15_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_138_mul z

end DimensionTen.Mod139
end
end OAI
