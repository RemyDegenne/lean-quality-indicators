public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMixedRadixMaskSelectedSquareBasisIdentityAtomTM

open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM

/-- GapCVP reduction support. -/
noncomputable def maskComputedWordEqualityComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (maskComputedWordEquality first second) := by
  have hleft := GapCVP.TMComposition.computableInPolyTime
    hfirst structuralPrefixWriterComputable
  have hright := GapCVP.TMComposition.computableInPolyTime
    hsecond structuralPrefixWriterComputable
  exact GapCVP.TMComposition.computableInPolyTime
    (pointwiseAppendComputable hleft hright)
    sourceQaryMaskSquarePairEqualityBitComputable

end SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM
end GapCVP
end
end
