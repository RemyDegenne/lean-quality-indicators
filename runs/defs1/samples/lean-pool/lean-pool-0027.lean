@[expose] public section

namespace BeyondBethe

open Complexity

/-- Runs nearby-coordinate summation for one step per input bit. -/
def machineNearbyMatrixFinalState (word : List Bool) : List Bool :=
  (machineNearbyMatrixStep)^[word.length] (machineNearbyMatrixInit word)

end BeyondBethe
end
