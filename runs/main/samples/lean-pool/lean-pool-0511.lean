@[expose] public section

namespace BeyondBethe

open Complexity

theorem machineFixedASecondRowRuler_mem_FP :
    machineFixedASecondRowRuler ∈ FP := by
  simpa only [machineFixedASecondRowRuler] using! machineCompose_mem_FP
    machineFixedARest₁_mem_FP machinePairFirst_mem_FP

end BeyondBethe
end
