public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFFiveFamilyPackedInitialCellDecoderTM

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLBoundedStates GapCVP.CLCellRows

open GapCVP.CLLocalWindows GapCVP.CLCellRowBounds GapCVP.CLFullTableauEmitter

open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding

open GapCVP.SourceUniformTuringTM GapCVP.SourceMachineCert

open GapCVP.OutputPolynomialCompositionClosure GapCVP.CLEmittedCNFTM GapCVP.CLWindowTruthTable

open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFUnaryPairIndexTM

open GapCVP.CNFUnaryPairIndexTotalRuntimeCert GapCVP.CNFFiveFamilyFlatCandidateGenerationTM

open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM

open GapCVP.CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM

open GapCVP.CNFFiveFamilyPackedInitialOffsetFeatureTM

open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM

theorem fiveFamilyFlatWholePackedInitialClauseRecordWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (position : Position (rowWidth bound machine original)) :
    fiveFlatWholePackedInitialClauseRecordWord
      bound machine
      (lengthPrefixedWord (List.replicate position.val true) ++
        lengthPrefixedWord original ++ suffix) =
      flatSourceClauseAnnotatedRecord
        (initialClause
          (paddedAcceptancePhaseSpecification
            bound machine original).input position) := by
  unfold fiveFlatWholePackedInitialClauseRecordWord
  rw [fiveFamilyPackedInitialSourceVariableCode_valid
    bound machine original suffix position,
    fiveFamilyFlatSourceVariableSingletonRecordWord_valid]
  rfl

end CNFFiveFamilyPackedInitialCellDecoderTM
end GapCVP
end
end
