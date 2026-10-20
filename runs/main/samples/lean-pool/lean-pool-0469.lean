@[expose] public section

namespace BeyondBethe

open Complexity

@[simp] theorem machineRationalTransposeMulVectorRemaining_pack (a b c d) :
    machineRationalTransposeMulVectorRemaining
      (machineRationalTransposeMulVectorPack a b c d) = a := by
  simp [machineRationalTransposeMulVectorRemaining,
    machineRationalTransposeMulVectorPack]

end BeyondBethe
end
