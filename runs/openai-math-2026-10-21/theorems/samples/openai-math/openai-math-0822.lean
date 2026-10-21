namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow

open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

theorem dummyView_left (k : MachineRegularDummyRow.Tape) :
    dummyView (dummyTapes k) = some k := by fin_cases k <;> rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock
end OAI
