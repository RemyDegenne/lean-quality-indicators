@[expose] public section

noncomputable section

open StateTransition (EvalsToInTime)

macro "compactMachineStepTac" "[" definitions:term,* "]" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [$[$definitions:term],*, Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CLNondeterminism

open Computability GapCVP.CLVerifier

/-- GapCVP reduction support. -/
structure GuessingExecution
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) where
  /-- GapCVP reduction support. -/
  certificate : List Bool
  /-- GapCVP reduction support. -/
  steps : ℕ
  steps_le : steps ≤ (guessTimePolynomial bound machine).eval x.length
  /-- GapCVP reduction support. -/
  run : FiniteRun (GuessStep bound machine x)
    (.guessing [])
    (.verifying certificate
      (Turing.haltList machine.tm (verifierOutput machine true)))
    steps

end CLNondeterminism
end GapCVP
end
end
