namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFieldProfile

open Turing

section Transport

variable {K Λ σ τ : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem statement_roundtrip (e : σ ≃ τ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ τ) :
    MachineControl.statement id e (MachineControl.statement id e.symm q) = q := by
  induction q <;> simp_all [MachineControl.statement]

end Transport
end UniqueGamesTheorem.Foundations.Complexity.MachineFieldProfile
end OAI
