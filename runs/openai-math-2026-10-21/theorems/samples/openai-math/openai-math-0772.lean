namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

theorem tableWords_decomposition (F : Formula) :
    GraphTables.tableWords (RawInitialTables.table F) =
      [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
        clauseOutput F.«variables» 0 F.clauses ++
          RawInitialRows.dummyWords F.«variables» F.clauses.length := by
  rw [RawInitialRows.tableWords_eq, clauseOutput_numbered]

end IndependentSetsGames.Foundations.PCP.RawInitialMachineLoopData
end OAI
