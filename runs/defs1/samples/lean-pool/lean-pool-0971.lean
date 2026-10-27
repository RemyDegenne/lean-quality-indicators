@[expose] public section

namespace BeyondBethe

open Complexity

/-- Concatenates four copies of a word for row-division width padding. -/
def machineRationalRowDividePadFour (word : List Bool) : List Bool :=
  machineRationalRowDividePadTwo word ++ machineRationalRowDividePadTwo word

end BeyondBethe
end
