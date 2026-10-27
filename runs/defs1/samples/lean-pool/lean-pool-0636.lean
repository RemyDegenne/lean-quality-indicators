@[expose] public section

namespace BeyondBethe

open Complexity

/-- Add the computed raw smoothing increment to every normalized matrix entry. -/
def machineSmoothedMatrixCode (word : List Bool) : List Bool :=
  machineMatrixAddDeltaEntries
    (pair (machineSmoothedMatrixDeltaRawCode word)
      (machineSmoothedMatrixNormalizedCode word))

end BeyondBethe
end
