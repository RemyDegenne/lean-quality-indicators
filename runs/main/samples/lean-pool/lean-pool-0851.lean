@[expose] public section

namespace BeyondBethe

open Complexity

theorem machineDirectedLogUpperRawCode_mem_FP :
    machineDirectedLogUpperRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineDirectedLogIntegerUpperCode_mem_FP
    machineDirectedLogResidualUpperCode_mem_FP
  simpa only [machineDirectedLogUpperRawCode] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

end BeyondBethe
end
