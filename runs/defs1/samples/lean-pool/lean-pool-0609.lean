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
def delimitedCompareSecondPrefixStatement :
    Turing.TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 12)
      DelimitedPairComparisonState :=
  delimitedComparePeekFirst 0
    (delimitedComparePop 0
      (delimitedComparePushFirst 7
        (delimitedComparePushConstant 8 true
          (.branch (fun state => state.first.getD false)
            (delimitedComparePushConstant 3 true
              (delimitedCompareGoto 2))
            (delimitedCompareGoto 3)))))
    (delimitedCompareSetOutcome .invalid 7)

end CNFEncodedClauseSort
end GapCVP
end
end
