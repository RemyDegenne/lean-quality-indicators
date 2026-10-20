@[expose] public section

namespace BeyondBethe

open Complexity

/-- Computes the next carry from the two operand heads and the current carry. -/
def machineBinaryAddNextCarry (state : List Bool) : List Bool :=
  machineFullAdderCarry
    (machineHeadBit (machineBinaryAddX state))
    (machineHeadBit (machineBinaryAddY state))
    (machineBinaryAddCarry state)

end BeyondBethe
end
