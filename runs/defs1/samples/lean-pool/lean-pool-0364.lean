@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the four-core query payload following both row indices. -/
def machineFourCoreRest₂ (word : List Bool) : List Bool :=
  machinePairSecond (machineFourCoreRest₁ word)

end BeyondBethe
end
