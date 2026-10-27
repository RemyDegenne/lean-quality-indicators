@[expose] public section

namespace BeyondBethe

open Complexity

/-- Convert the flattened binary index to a unary ruler bounded by the input word. -/
def machineBetheFlatIndexRuler (word : List Bool) : List Bool :=
  machineBoundedUnary (pair word (machineBetheFlatIndexBits word))

end BeyondBethe
end
