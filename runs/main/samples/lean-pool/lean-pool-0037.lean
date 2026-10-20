@[expose] public section

namespace BeyondBethe

open Complexity

theorem machineEllipsoidDimensionSquareRawCode_mem_FP :
    machineEllipsoidDimensionSquareRawCode ∈ FP := by
  simpa only [machineEllipsoidDimensionSquareRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineEllipsoidDimensionRawCode_mem_FP
        machineEllipsoidDimensionRawCode_mem_FP)
      machineRawRatMulCode_mem_FP

end BeyondBethe
end
