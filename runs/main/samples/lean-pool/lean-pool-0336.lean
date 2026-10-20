open scoped HahnSeries

universe v

public noncomputable section

namespace FLLM24

open Berarducci

variable {K : Type v} [Field K]

variable [CharZero K] in
theorem isMutuallyRandom_iff {ι : Type*} (b : ι → Series K) :
    IsMutuallyRandom b ↔ IsMutuallySupportRandom b ∨ IsMutuallyCoefficientRandom b :=
  (Iff.rfl)

end FLLM24
end
