public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace PhysicalRightHandSideTM

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM

open GapCVP.SourceFourFamilyBooleanPredicateTM

open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM

open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryPhysicalRowBasisDivisionTM

open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalColumnOrder

open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM GapCVP.MatrixEntrySemantics

open GapCVP.PhysicalRowOrderProjection

/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRightHandSideCellDegreeUnaryComputable :
    BitTM
      physicalRightHandSideCellDegreeUnary :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable

end PhysicalRightHandSideTM
end GapCVP
end
end
