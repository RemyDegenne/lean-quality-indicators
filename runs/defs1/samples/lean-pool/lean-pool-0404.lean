@[expose] public section

namespace BeyondBethe

open Complexity

/-- Perform the exact rational central ellipsoid update and then round at the supplied
precision. -/
def machineScheduledRoundedEllipsoidCentralUpdateCode
    (word : List Bool) : List Bool :=
  machineScheduledRoundedEllipsoidCode
    (pair (machineScheduledCentralPrecision word)
      (machineRationalEllipsoidCentralUpdateCode
        (machineScheduledCentralStateAndCut word)))

end BeyondBethe
end
