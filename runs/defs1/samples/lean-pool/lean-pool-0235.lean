@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extract the oracle input payload following the dimension word. -/
def machineBetheOracleRest (word : List Bool) : List Bool :=
  machinePairSecond word

end BeyondBethe
end
