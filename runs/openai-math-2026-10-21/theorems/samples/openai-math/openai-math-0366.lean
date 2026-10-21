namespace OAI

namespace DFVSGames.Foundations.PCP.AlphabetTable.Table

variable {q : Nat}

@[simp] theorem build_darts (input : GenericGraphTables.Table q) :
    (build input).darts = Enumeration.dartCount input.darts q := rfl

end DFVSGames.Foundations.PCP.AlphabetTable.Table
end OAI
