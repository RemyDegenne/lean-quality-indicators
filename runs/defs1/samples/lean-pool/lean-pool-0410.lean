@[expose] public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFUnaryPairIndexTotalCert

open Computability Turing GapCVP.CNFUnaryPairIndexTM

/-- GapCVP reduction support. -/
def unaryPairComparedConfiguration
    (first second matched : ℕ) :
    actualUnaryPairIndexMachine.Cfg :=
  if first < second then
    unaryPairConfiguration 5 [] []
      (List.replicate (second - first) true)
      (List.replicate (matched + first) true)
      (List.replicate (matched + first) true)
      [] [] [] []
  else
    unaryPairConfiguration 3 []
      (List.replicate (first - second) true) []
      (List.replicate (matched + second) true)
      (List.replicate (matched + second) true)
      [] [] [] []

end CNFUnaryPairIndexTotalCert
end GapCVP
end
end
