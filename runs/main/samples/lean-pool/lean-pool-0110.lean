@[expose] public section

namespace BeyondBethe

open Complexity

theorem machineOptimizerInteriorExponentGuard_mem_FP :
    machineOptimizerInteriorExponentGuard ∈ FP := by
  simpa only [machineOptimizerInteriorExponentGuard] using!
    machineIteratedBinaryWidth_mem_FP 6

end BeyondBethe
end
