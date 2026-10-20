public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace GaussianOutputSerializerTM

open Turing GapCVP.Core GapCVP.Factor400BinaryInstanceBridge GapCVP.BinaryEncoding

open GapCVP.SourceMachineCert GapCVP.CLStructuralPrefixWriter

open GapCVP.CLStructuralAtomicNaturalWriter GapCVP.CNFFlatPhysicalBinaryAppendTM

open GapCVP.BinaryDimensionTM GapCVP.BinaryExplicitAffineRows GapCVP.BinaryStructuralRecordTM

open GapCVP.BinaryGaussianStructuralAtomTM GapCVP.BinaryGaussianStructuralRecordIndex

open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.GaussianPhysicalWordRankIndexTM

open GapCVP.GaussianPackedStateTargetAtomTM GapCVP.GaussianPackedStateBasisAtomTM

open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePackedTraceCorrectness

open GapCVP.Factor400BinaryCompactPhysicalGaussianOutputSerializerTM GapCVP.CanonicalMatrixShape

open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap

open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityGaussianStructuralAtomComputer
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced) :
    ConstructiveStructuralAtomComputer :=
  compactPhysicalGaussianStructuralAtomComputerPack
    (paperGaussianStructuralAtomOutput
      shape radius reduced)
    (paperVariableArityGaussianStructuralAtomComputable
      shape radiusComputer reducedComputer)

end GaussianOutputSerializerTM
end GapCVP
end
end
