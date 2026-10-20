@[expose] public section

namespace BeyondBethe

open Complexity

namespace MachineRAMBridge

open RAM.RegisterStore.Machine

theorem languageFlag_mem_FP_of_paddedRamProgram
    (count : ℕ) {L : Language}
    [DecidablePred (fun word => word ∈ L)]
    (program : RAM.Program) (p : Polynomial ℕ)
    (hdecides : program.DecidesInTime (paddedLanguage count L) p.eval) :
    languageFlag L ∈ Complexity.FP := by
  have hpadded : languageFlag (paddedLanguage count L) ∈ Complexity.FP :=
    languageFlag_mem_FP_of_ramProgram program p hdecides
  have hcomposed :
      (fun word => languageFlag (paddedLanguage count L)
        (prefixZeroRegisters count word)) ∈ Complexity.FP :=
    machineCompose_mem_FP (prefixZeroRegisters_mem_FP count) hpadded
  have heq : (fun word => languageFlag (paddedLanguage count L)
      (prefixZeroRegisters count word)) = languageFlag L := by
    funext word
    exact languageFlag_padded_prefix count L word
  rwa [heq] at hcomposed

end MachineRAMBridge
end BeyondBethe
end
