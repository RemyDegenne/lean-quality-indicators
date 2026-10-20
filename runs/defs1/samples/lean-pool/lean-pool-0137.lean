@[expose] public section

namespace BeyondBethe

open Complexity

/-- Initializes the outer scan with reverse-ordered row candidates and no selected pairs. -/
def machineMatchingOuterInit (optimizer : List Bool) : List Bool :=
  machineMatchingOuterPack (machineMatchingReverseRange optimizer) [] optimizer

end BeyondBethe
end
