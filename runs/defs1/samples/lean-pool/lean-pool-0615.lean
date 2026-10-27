@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the unary row ruler from an executable affine matrix-entry request. -/
def machineExecutableMatrixEntryRow (word : List Bool) : List Bool :=
  machinePairFirst word

end BeyondBethe
end
