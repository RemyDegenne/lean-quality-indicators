@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the current row ruler from a Kuhn call control word. -/
def machineKuhnCallRow (control : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machineKuhnControlPayload control)))

end BeyondBethe
end
