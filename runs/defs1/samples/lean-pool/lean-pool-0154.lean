public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace ShiftedTupleBetaTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert

open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceCanonicalFixedWordTuringTM

open GapCVP.SourceIndexedClauseLookupTM GapCVP.SourceIndexedClauseSignTM

open GapCVP.SourceFourFamilyBooleanPredicateTM

open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows

open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalRowBasisDivisionTM

open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingTM

open GapCVP.SourcePreprocessingSemantics GapCVP.ClauseOffsetTM

/-- Encode a rejected literal position's binary weight in unary. -/
def paperShiftedTupleRejectedWeightedUnary
    (ranks : PaperVariableArityShiftedTupleRankComputers)
    (position : Fin 3) : List Bool → List Bool :=
  paperShiftedTupleGuardedSourceWord
    (paperShiftedTupleRejectedPositionBit ranks position)
    (paperShiftedTupleConstantUnary (2 ^ position.val))

end ShiftedTupleBetaTM
end GapCVP
end
end
