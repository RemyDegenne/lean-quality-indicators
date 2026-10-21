namespace OAI

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

theorem prepared_reverse (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .reverseIndex =
      encodeWord table.rows[e].reverseIndex.val ++ base .reverseIndex := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program
end OAI
