@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the reversed accumulated column entries. -/
def machineRationalMatrixColumnAccumulator
    (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

end BeyondBethe
end
