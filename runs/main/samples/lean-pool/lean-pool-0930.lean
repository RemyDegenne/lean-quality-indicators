@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace WordReduction

namespace Pairing

namespace MarkedBoundaryPairContraction

theorem contract {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (step : MarkedBoundaryPairContraction tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (classified : ReductionToken.AllClassified tokens)
    (protectedNodup : (ReductionToken.protectedNames tokens).Nodup)
    (valid : (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    MarkedBoundaryPairContractionResult step valid := by
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated step.expand_isRotated_sourceWord
  let validSourceWord :
      (Dyck.oneFace
        (BoundaryPairContraction.sourceWord
          step.first step.second
          step.firstNegative step.secondNegative
          (ReductionToken.expand step.tailTokens))).IsSurfaceValid :=
    sourceRotation.isSurfaceValid valid
  let witness :=
    BoundaryPairContraction.exists_normalizationEquivalent
      step.first step.second step.firstNegative step.secondNegative
      (ReductionToken.expand step.tailTokens)
      step.first_ne_second step.first_not_mem_tail step.second_not_mem_tail validSourceWord
  let validTargetWord := Classical.choose witness
  have hequivalentWord :=
    Classical.choose_spec witness
  have htarget :
      ReductionToken.expand step.targetTokens =
        BoundaryPairContraction.targetWord
          step.first step.second step.first_ne_second
          (ReductionToken.expand step.tailTokens) :=
    step.expand_targetTokens
  have targetValid :
      (Dyck.oneFace (ReductionToken.expand step.targetTokens)).IsSurfaceValid := by
    rw [htarget]
    exact validTargetWord
  refine
    { targetValid := targetValid
      targetSeparated := step.targetTokens_isSeparated separated
      targetClassified := step.targetTokens_allClassified classified
      targetProtectedNodup :=
        step.targetTokens_protectedNames_nodup protectedNodup
      equivalent := ?_ }
  have hrotation :
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (ReductionToken.expand tokens), valid⟩
        ⟨Dyck.oneFace
          (BoundaryPairContraction.sourceWord
            step.first step.second
            step.firstNegative step.secondNegative
            (ReductionToken.expand step.tailTokens)), validSourceWord⟩ :=
    NormalizationEquivalent.ofSignedIso sourceRotation
  have hchain := hrotation.trans hequivalentWord
  simpa only [htarget] using hchain

end MarkedBoundaryPairContraction
end Pairing
end WordReduction
end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
