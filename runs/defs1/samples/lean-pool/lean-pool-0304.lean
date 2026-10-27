@[expose] public section

namespace BeyondBethe

open Complexity

/-- Normalizes the divided row entry into its rational entry encoding. -/
def machineRationalRowDivideEntry (state : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineRationalRowDivideRawEntry state)

end BeyondBethe
end
