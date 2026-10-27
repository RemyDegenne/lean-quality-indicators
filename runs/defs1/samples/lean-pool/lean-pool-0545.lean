public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace PhysicalGlobalRefinementCoefficientTM

open scoped BigOperators

open Turing GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM

open GapCVP.SourceFourFamilyBooleanPredicateTM

open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM

open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryExplicitAffineSystem

open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.FormulaBridge GapCVP.PhysicalFamilyRowTM

open GapCVP.PhysicalFamilyMarkerTM GapCVP.PhysicalRowOrderProjection

open GapCVP.PhysicalRightHandSideTM

attribute [local instance] Classical.propDecidable

/-- GapCVP reduction support. -/
def physicalColumnGridRankUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    physicalColumnGridQuotientUnary
    physicalCoefficientGridCardinalityUnary

end PhysicalGlobalRefinementCoefficientTM
end GapCVP
end
end
