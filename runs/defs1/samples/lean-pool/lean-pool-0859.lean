@[expose] public section

namespace BeyondBethe

open Complexity

/-- Packs the unprocessed selected-pair list, accumulated conflict bit, and fixed request. -/
def machineDisjointPack
    (remaining conflict source : List Bool) : List Bool :=
  pair remaining (pair conflict source)

end BeyondBethe
end
