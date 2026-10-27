@[expose] public section

namespace BeyondBethe

open Complexity

/-- Runs the update scan for the length of the requested unary index ruler. -/
def machineListUpdateScanFinalState (word : List Bool) : List Bool :=
  (machineListUpdateScanStep)^[(machineListUpdateRuler word).length]
    (machineListUpdateScanInit word)

end BeyondBethe
end
