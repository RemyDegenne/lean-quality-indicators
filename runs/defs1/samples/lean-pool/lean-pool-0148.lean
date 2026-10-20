public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace ClauseOffsetTM

open Turing

open scoped BigOperators

open GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceStructuralTuringTM

open GapCVP.SourceMachineCert GapCVP.OutputBoundedDependentRecordFold

open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceIndexedClauseLookupTM

open GapCVP.SourceNormalizedVariableRankScanTM GapCVP.CNFFlatPhysicalBinaryAppendTM

open GapCVP.CNFBoundedRecordFoldTM GapCVP.CLStructuralPrefixWriter GapCVP.BinaryDimensionTM

open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics

open GapCVP.SourcePreprocessingTM

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityRetainedClauseCountUnaryComputable :
    BitTM
      paperRetainedClauseCountUnary :=
  paperPreprocessingFinalFieldComputable 2

end ClauseOffsetTM
end GapCVP
end
end
