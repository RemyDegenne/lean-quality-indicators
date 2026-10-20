@[expose] public section

namespace BeyondBethe

open Complexity

theorem machineKuhnBuildChosenMate_mem_FP :
    machineKuhnBuildChosenMate ∈ Complexity.FP := by
  have hfallback := machineCompose_mem_FP machineKuhnTopFrame_mem_FP
    machineKuhnBuildFrameFallback_mem_FP
  exact machineIfHead_mem_FP machineKuhnRetSuccess_mem_FP
    machineKuhnRetMate_mem_FP hfallback

end BeyondBethe
end
