namespace OAI

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

namespace DFVSGames.BinaryTokenMachine

open Turing

open DFVSGames.Foundations.Complexity

open MachineComposition

open DFVSGames.Reduction.MachineTransfer

open BinaryFormula BinaryEncoding

theorem tokenTrace (formula : Formula) :
    (advance machine.step)^[13 * formula.clauses.length +
        3 * namesBitSize formula.clauses + 3]
      (some (initList machine (formulaBits formula))) =
      some (haltList machine (tokens formula.clauses)) := by
  rw [show 13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3 =
    (13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 2) + 1 by omega,
    Function.iterate_succ_apply', acceptTrace, advance_some, haltStep, haltList_eq]

end DFVSGames.BinaryTokenMachine
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
