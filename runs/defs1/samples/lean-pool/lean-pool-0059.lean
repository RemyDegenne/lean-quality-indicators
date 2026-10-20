@[expose] public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFEncodedClauseSort

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder

open GapCVP.CNFSortingDedup

/-- GapCVP reduction support. -/
def delimitedCompareOutcomeStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  .push 9 (fun state => encodedWordOrderingSecond state.outcome)
    (.push 9 (fun state => encodedWordOrderingFirst state.outcome)
      (delimitedCompareGoto 10))

end CNFEncodedClauseSort
end GapCVP
end
end
