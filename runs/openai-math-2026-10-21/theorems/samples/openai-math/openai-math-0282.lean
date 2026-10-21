namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition

open DFVSGames.Foundations.PCP

open MachineCloudPadding

theorem rowCastTapes (base : (k : MachinePaddingRows.Tape) → List (MachinePaddingRows.Alphabet k)) :
    MachineAlphabetTransport.tapes rowAlphabet_eq base = rowBoolTapes base := by
  funext k
  rw [transport_tapes_apply_inline_MachineVertexPadding]
  cases k <;> rfl

end DFVSGames.Foundations.Complexity.MachineVertexPadding
end OAI
