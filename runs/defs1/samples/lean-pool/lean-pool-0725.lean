@[expose] public section

namespace BeyondBethe

open Complexity

/-- Encode an accepted center with the false tag, or the final unaccepted ellipsoid with the
true tag. -/
def machineBetheFeasibilityStateResultCode
    (state : List Bool) : List Bool :=
  machineIfHead (machineHeadBit
      (machineBetheFeasibilityStateAccepted state))
    (pair [false]
      (machineRationalEllipsoidCenterWord
        (machineBetheFeasibilityStateEllipsoid state)))
    (pair [true] (machineBetheFeasibilityStateEllipsoid state))

end BeyondBethe
end
