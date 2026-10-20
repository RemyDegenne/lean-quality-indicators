@[expose] public section

namespace BeyondBethe

open Complexity

/-- Convert the unary affine dimension ruler to its binary length. -/
def machineBetheAffineEntryDimensionBits (word : List Bool) : List Bool :=
  machineLengthBits (machineBetheAffineEntryDimension word)

end BeyondBethe
end
