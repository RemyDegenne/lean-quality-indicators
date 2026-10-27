@[expose] public section

namespace BeyondBethe

open Complexity

/-- Uses the returned matching after success and the build continuation's fallback matching
after failure. -/
def machineKuhnBuildChosenMate (state : List Bool) : List Bool :=
  let frame := machineKuhnTopFrame state
  machineIfHead (machineKuhnRetSuccess state) (machineKuhnRetMate state)
    (machineKuhnBuildFrameFallback frame)

end BeyondBethe
end
