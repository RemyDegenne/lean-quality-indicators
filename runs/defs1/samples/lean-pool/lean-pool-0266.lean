public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace SourceFieldMomentOperationsTM

open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding

open GapCVP.SourceCanonicalFixedWordTuringTM

open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM

open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryFieldInverseAlgebra

open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalLagrangeCoefficientTM

open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.BinaryCompactPhysicalLagrangeFactorStreamTM

open GapCVP.BinaryCompactPhysicalLagrangeMomentWeightTM GapCVP.FormulaBridge

open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM

open GapCVP.PhysicalRefinementRowProjection

open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldArithmeticMachine

open GapCVP.Factor400BinaryConstructivePaperVariableAritySourceFieldOperationsMachine

/-- Encode the local offset of a physical family row. -/
def physicalFamilyRowLocalOffsetWord
    (family : Fin 4) : List Bool → List Bool :=
  unarySubtractionOutput sourceExplicitAffineCellRow
    (physicalFamilyStartUnary family)

end SourceFieldMomentOperationsTM
end GapCVP
end
end
