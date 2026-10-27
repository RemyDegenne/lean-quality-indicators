@[expose] public section

namespace BeyondBethe

open Complexity

/-- Builds the encoded complete index range from the unary input dimension. -/
def machineKuhnInitColumns (matrix : List Bool) : List Bool :=
  machineUnaryRangeCode (machineKuhnInitDimension matrix)

end BeyondBethe
end
