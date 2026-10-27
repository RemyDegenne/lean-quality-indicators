@[expose] public section

namespace BeyondBethe

open Complexity

/-- Dispatches nonnegative matrices to the completed algorithm and returns zero for a failed
sign test. -/
def machineCompletedAlgorithmCode
    (positiveMachine : List Bool → List Bool) (χ : ℚ)
    (word : List Bool) : List Bool :=
  machineIfHead (machineMatrixNonnegativeBit word)
    (machineCompletedNonnegativeBranchCode positiveMachine χ word)
    (rationalBinaryCode 0)

end BeyondBethe
end
