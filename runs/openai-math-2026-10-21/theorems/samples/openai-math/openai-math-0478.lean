namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceMachine

open Turing

open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

theorem fieldStep_true (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), fieldTapes source destination base (true :: input) output⟩ =
      some ⟨some loopLabel, (ambient, some true),
        fieldTapes source destination base input (true :: output)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (fieldTapes source destination base (true :: input) output)) = _
  rw [atLoop]
  simp [fieldLoop, TM2.stepAux, hne, update_field_source, update_field_destination]

end UniqueGamesTheorem.Foundations.Hastad.SourceMachine
end
end OAI
