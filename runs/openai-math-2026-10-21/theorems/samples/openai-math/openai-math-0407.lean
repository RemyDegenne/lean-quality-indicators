namespace OAI

section

namespace MinUncutGames.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow

open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

theorem originalMemory_update (graph : List Bool) (x : Nat) (output output' : List Bool) :
    Function.update (originalMemory graph x output) (9 : MachineRegularOriginalClean.Tape) output' =
      originalMemory graph x output' := by funext j; fin_cases j <;> rfl

end MinUncutGames.Foundations.Complexity.MachineRegularVertexBlock
end
end OAI
