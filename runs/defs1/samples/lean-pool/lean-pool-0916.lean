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

namespace CLExactVerifierTransition

open Computability GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLExactStackRules

open GapCVP.CLCompleteLocalCompiler GapCVP.CLFiniteShiftWindows

/-- GapCVP reduction support. -/
noncomputable def AllVerifierStackWindows
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hint : FiniteVerifierHint machine.tm) : Bool :=
  @decide (
  ∀ stack : machine.tm.K,
    AllStackShiftWindows machine.tm width (hint stack)
      (canonicalStackAtoms machine stack (first.stk stack)
        (stackAtomSupported_supportedValues machine first hfirst stack))
      (canonicalStackAtoms machine stack (next.stk stack)
        (stackAtomSupported_supportedValues machine next hnext stack))
  ) (Classical.propDecidable _)

end CLExactVerifierTransition
end GapCVP
end
end
