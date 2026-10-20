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
def delimitedCompareConfiguration (phase : Fin 12)
    (outcome : EncodedWordOrdering)
    (input firstCounter firstReversed secondCounter secondReversed
      firstForward secondForward source sourcePrefix output : List Bool) :
    delimitedPairComparisonMachine.Cfg where
  l := some phase
  var := ⟨none, none, outcome⟩
  stk := ![input, firstCounter, firstReversed,
    secondCounter, secondReversed, firstForward, secondForward,
    source, sourcePrefix, output]

end CNFEncodedClauseSort
end GapCVP
end
end
