@[expose] public section

namespace BeyondBethe

open Complexity

/-- Consumes one row and stores its selected column entry while retaining the index and bound. -/
def machineRationalMatrixColumnAdvance
    (state : List Bool) : List Bool :=
  machineRationalMatrixColumnPack
    (machineListTail (machineRationalMatrixColumnRemaining state))
    (machineRationalMatrixColumnNextAccumulator state)
    (machineRationalMatrixColumnColumn state)
    (machineRationalMatrixColumnBound state)

end BeyondBethe
end
