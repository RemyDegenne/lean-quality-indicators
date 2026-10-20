public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace BinaryCompactPhysicalFieldWordXorTM

open Turing Polynomial GapCVP.Core.EffectiveBinaryField GapCVP.BinaryEncoding

open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.GaussianXorWorker GapCVP.BinaryFieldBasis

open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryModularReductionTM

open GapCVP.BinaryPhysicalCellGridWordTM GapCVP.BinaryPhysicalLagrangeCoefficientTM

open GapCVP.BinaryPhysicalWordRuntimeDegreeTM

theorem compactPhysicalFieldWordXorWithDegree_valid
    (degreeWorker left right : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (degree : ℕ)
    (leftWord rightWord : GapCVP.Core.EffectiveBinaryField.Word degree)
    (hdegree : degreeWorker.output input =
      List.replicate degree true)
    (hleft : left.output input = finiteWordBits leftWord)
    (hright : right.output input = finiteWordBits rightWord) :
    compactPhysicalFieldWordXorWithDegree
        degreeWorker left right input =
      finiteWordBits
        (compactPhysicalFieldWordXorValue leftWord rightWord) := by
  unfold compactPhysicalFieldWordXorWithDegree
  rw [maskDynamicGridRecordCatalogueOutput_valid
    (compactPhysicalFieldWordXorDegreeWidth degreeWorker)
    (compactPhysicalFieldWordXorCandidateComputable left right)
    input degree hdegree]
  simp_rw [compactPhysicalFieldWordXorCandidate_query]
  rw [hleft, hright, ← List.map_eq_flatMap]
  exact finiteWordBits_compactPhysicalFieldWordXorValue
    leftWord rightWord

end BinaryCompactPhysicalFieldWordXorTM
end GapCVP
end
end
