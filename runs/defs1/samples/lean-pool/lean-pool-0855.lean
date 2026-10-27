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

/-- GapCVP reduction support. -/
def physicalFamilyMomentPowerWord
    (family : Fin 4) (base : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  compactPhysicalLagrangeFactorProductWord
    (physicalFamilyRowMomentWidth family)
    physicalCellSelectedModulusComputer
    paperVariableArityPhysicalMomentUnitComputer
    physicalMomentOriginalSourceComputer
    (compactPhysicalLagrangeMomentNodeFactorComputer base)

end SourceFieldMomentOperationsTM
end GapCVP
end
end
