public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace SourceIndexedClauseLookupTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold

open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceMixedRadixDimensionRowMajorIndexTM

open GapCVP.SourceMixedRadixPolynomialPaddedDescriptorFoldTM

open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.CLStructuralPrefixWriter

open GapCVP.CNFCappedUnaryPairArithmeticTM GapCVP.CNFFlatPhysicalBinaryAppendTM

/-- GapCVP reduction support. -/
@[expose]
def sourceOriginalIndexedLiteralVariableOutput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (firstFieldContents input)

end SourceIndexedClauseLookupTM
end GapCVP
end
end
