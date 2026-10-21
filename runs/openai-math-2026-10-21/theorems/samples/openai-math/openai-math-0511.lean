namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition

open UniqueGamesTheorem.Foundations.PCP

open MachineCloudPadding

theorem affineOutputTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (coefficient : Nat) (seed scan restore : Label d) (exit : Option (Label d))
    (atSeed : program (σ := σ) d hd seed = MachineUnaryAffineAt.seed (σ := σ × Bool) .output 0 scan)
    (atScan : program (σ := σ) d hd scan = MachineUnaryAffineAt.scan (σ := σ × Bool) .power .scratch .output
      coefficient scan restore)
    (atRestore : program (σ := σ) d hd restore = Reduction.MachineTransfer.loopAt (σ := σ × Bool)
      .scratch .power id false restore exit)
    (input output vertex edge level fuel relation : List Bool) (m : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[1 + 2 * (m + 1)]
      (some ⟨some seed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level fuel relation⟩) =
      some ⟨exit, ((ambient, false), none),
        memory input (encodeWord (coefficient * m) ++ output) vertex edge
          (encodeWord m) level fuel relation⟩ := by
  have hs : (advance (TM2.step (program d hd)))^[1]
      (some ⟨some seed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level fuel relation⟩) =
      some ⟨some scan, ((ambient, false), register),
        memory input (encodeWord 0 ++ output) vertex edge (encodeWord m) level fuel relation⟩ := by
    change some (TM2.stepAux (program d hd seed) _ _) = _
    rw [atSeed]
    simp [MachineUnaryAffineAt.seed, Reduction.MachineSubstitution.stepAux_pushWord,
      TM2.stepAux, encodeWord, memory]
  let base := memory input output vertex edge (encodeWord m) level fuel relation
  have ht := MachineUnaryAffineAt.affineTrace Tape.power Tape.scratch Tape.output
    (by decide) (by decide) (by decide) coefficient scan restore exit (program d hd)
    atScan atRestore base m 0 [] output (ambient, false) register
  have hstart : MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output base
      (encodeWord m ++ []) [] (encodeWord 0 ++ output) =
      memory input (encodeWord 0 ++ output) vertex edge (encodeWord m) level fuel relation := by
    funext k
    cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, base, memory]
  have hfinish : MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output base
      (encodeWord m ++ []) [] (encodeWord (coefficient * m + 0) ++ output) =
      memory input (encodeWord (coefficient * m) ++ output) vertex edge
        (encodeWord m) level fuel relation := by
    funext k
    cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, base, memory]
  rw [hstart, hfinish] at ht
  exact appendTrace _ hs ht

end UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding
end OAI
