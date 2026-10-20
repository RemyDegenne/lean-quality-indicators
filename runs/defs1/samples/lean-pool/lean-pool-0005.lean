public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace BinaryCompactPhysicalLagrangeNestedNodeTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryExplicitAffineRows

open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalWordRuntimeDegreeTM

/-- GapCVP reduction support. -/
def compactPhysicalLagrangeNestedNodeOriginalSource :
    List Bool → List Bool :=
  sourceExplicitAffineCellOriginalSource ∘
    compactPhysicalLagrangeNestedNodeOuterCell

end BinaryCompactPhysicalLagrangeNestedNodeTM
end GapCVP
end
end
