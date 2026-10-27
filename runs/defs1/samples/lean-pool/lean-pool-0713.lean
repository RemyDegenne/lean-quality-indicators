@[expose] public section

namespace BeyondBethe

open Complexity

/-- Tests whether the current matrix entry differs from zero in raw rational arithmetic. -/
def machineMatrixSupportNonzeroFlag (state : List Bool) : List Bool :=
  machineRawRatNeBit
    (pair (machineMatrixRawSumEntry state)
      (rawRatBinaryCode RawRat.zero))

end BeyondBethe
end
