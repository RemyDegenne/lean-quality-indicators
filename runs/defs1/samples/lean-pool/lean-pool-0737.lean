@[expose] public section

noncomputable section

open StateTransition (EvalsToInTime)

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CLCompleteVerifierSimulation

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLBoundedStates

open GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLCellRowBounds GapCVP.CLLocalWindows

open GapCVP.CLExactLocalRules GapCVP.CLExactStackRules GapCVP.CLExactVerifierTransition

open GapCVP.CLTableauSimulationCert GapCVP.CLFullTableauEmitter

/-- GapCVP reduction support. -/
def completePayloadWindow
    (tm : Turing.FinTM2)
    (window : CompletePhaseWindow tm)
    (offset : Fin (blockSize tm)) :
    PairedInputTag × PairedInputTag × PairedInputTag × PairedInputTag :=
  (phaseLeftOffset tm
      (completeIsFirstBlock tm window.2.1)
      window.1.payload window.2.1.payload offset,
    window.2.1.payload offset,
    phaseRightOffset tm
      window.2.1.payload window.2.2.1.payload offset,
    window.2.2.2.payload offset)

end CLCompleteVerifierSimulation
end GapCVP
end
end
