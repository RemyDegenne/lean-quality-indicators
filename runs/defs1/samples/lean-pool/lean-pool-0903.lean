@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the payload following the row ruler of an executable matrix-entry request. -/
def machineExecutableMatrixEntryRest (word : List Bool) : List Bool :=
  machinePairSecond word

end BeyondBethe
end
