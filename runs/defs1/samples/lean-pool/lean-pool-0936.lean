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

section

/-- GapCVP reduction support. -/
noncomputable def gapCVPWellFormed (I : GapCVPInstance) : Bool :=
  @decide (
  0 < I.dimension ∧ I.basis.det ≠ 0 ∧ 0 < I.radius
  ) (Classical.propDecidable _)

end
end GapCVP
end
end
