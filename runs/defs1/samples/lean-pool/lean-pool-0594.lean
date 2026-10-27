@[expose] public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFNaturalOrderCertifiedComparator

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder

open GapCVP.CNFSortingDedup GapCVP.CNFEncodedClauseSort GapCVP.CNFNaturalOrderComparator

open GapCVP.CNFNaturalOrderTotalComparator

/-- Finish with an invalid result when the first record has an undelimited length prefix. -/
def certifiedNaturalMissingFirstTrace (count : ℕ) :
    EvalsToInTime delimitedNaturalComparisonMachine.step (naturalCompareConfiguration 0 .invalid
        (List.replicate count true) [] [] [] [] [] [] [] [] [])
      (some (Turing.haltList delimitedNaturalComparisonMachine
        (sourcePreservingDelimitedNaturalComparisonWord
          (List.replicate count true))))
      (24 * ((List.replicate count true).length + 1) + 24) := by
  have hscan :
      EvalsToInTime delimitedNaturalComparisonMachine.step
        (naturalCompareConfiguration 0 .invalid
          (List.replicate count true) [] [] [] [] [] [] [] [] [])
        (some (naturalCompareConfiguration 7 .invalid
          [] (List.replicate count true) [] [] [] [] []
          (List.replicate count true)
          (List.replicate count true) []))
        (count + 1) := by
    simpa only [FinTM2.step, Fin.isValue, List.append_nil] using
        certifiedNaturalFirstMissingPrefixTrace .invalid count [] [] [] [] [] [] [] [] []
  have hfinish := certifiedNaturalFinishTrace .invalid
    [] (List.replicate count true) [] [] [] [] []
    (List.replicate count true) (List.replicate count true) []
  have hrestored :
      delimitedCompareRestoredWord .invalid []
        (List.replicate count true) (List.replicate count true) [] =
      sourcePreservingDelimitedNaturalComparisonWord
        (List.replicate count true) := by
    simp only [delimitedCompareRestoredWord, List.length_nil, List.length_replicate, zero_add,
        List.reverse_replicate, List.append_nil, sourcePreservingDelimitedNaturalComparisonWord,
            lengthPrefixedWord,
        delimitedNaturalPairOrdering_missingFirst, List.append_assoc, List.cons_append]
  rw [hrestored] at hfinish
  have hfull := EvalsToInTime.trans delimitedNaturalComparisonMachine.step _ _ _ _ _ hscan hfinish
  apply rebound hfull
  simp only [List.length_replicate, List.length_nil]
  omega

end CNFNaturalOrderCertifiedComparator
end GapCVP
end
end
