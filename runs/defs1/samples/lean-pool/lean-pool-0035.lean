@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the replacement entry from a rational matrix-update request. -/
def machineRationalMatrixUpdateReplacement (word : List Bool) : List Bool :=
  machinePairFirst (machineRationalMatrixUpdatePayload word)

end BeyondBethe
end
