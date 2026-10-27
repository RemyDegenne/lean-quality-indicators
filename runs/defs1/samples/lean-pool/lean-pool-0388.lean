@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the unary row index from a direction-update row request. -/
def machineDirectionRowIndex (word : List Bool) : List Bool :=
  machinePairFirst word

end BeyondBethe
end
