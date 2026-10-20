@[expose] public section

namespace BeyondBethe

open Complexity

/-- Encodes a square rational matrix together with the raw-rational increment to add. -/
def machineMatrixAddDeltaCanonicalInput {n : ℕ}
    (delta : RawRat) (A : Matrix (Fin n) (Fin n) ℚ) : List Bool :=
  pair (rawRatBinaryCode delta)
    (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)

end BeyondBethe
end
