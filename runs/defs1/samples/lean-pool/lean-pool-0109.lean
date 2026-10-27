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

namespace FiniteRun

/-- GapCVP reduction support. -/
noncomputable def single {α : Type} {transition : α → α → Type}
    {first last : α} (h : transition first last) :
    FiniteRun transition first last 1 :=
  .tail (.refl first) h

end FiniteRun
end CLNondeterminism
end GapCVP
end
end
