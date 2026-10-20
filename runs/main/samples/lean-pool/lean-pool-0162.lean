@[expose] public section

namespace BeyondBethe

open Complexity

@[simp] theorem rawOptimizerBitBound_value (B : ℕ) :
    (rawOptimizerBitBound B).value = B := by
  simp [rawOptimizerBitBound]

end BeyondBethe
end
