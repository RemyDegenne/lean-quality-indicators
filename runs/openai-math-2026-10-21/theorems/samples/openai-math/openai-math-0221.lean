namespace OAI

namespace BinPackingGames.Foundations.Complexity.TableIterationFiniteAlphabet

open PCP MachineFiniteAlphabet

variable (H : RoundTables.BaseTable)
  (body : Turing.TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
    (RoundTables.build H))
  (finiteBody : FiniteAlphabet body.tm)

include finiteBody

theorem table : FiniteAlphabet (MachineTableIteration.tableCertificate H body).tm :=
  composeBits MachineTableIteration.initialCertificate
    (MachineTableIteration.computableInPolyTime H body) initial (iteration H body finiteBody)

end BinPackingGames.Foundations.Complexity.TableIterationFiniteAlphabet
end OAI
