@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace WordReduction

namespace Pairing

namespace MarkedResidualCancellablePair

/-- Commute a completed crosscap out of a lifted pair, producing a strict interval shortening. -/
noncomputable def shortenCrosscapBlock {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (carrier : Fin (n + 1))
    (carrierNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.crosscap carrier
          carrierNegative) ::
          insideTokens) :
    MarkedResidualPairShortening pair state := by
  have residualInside :
      ReductionToken.residualDarts insideTokens = [] := by
    have h := pair.residual_between
    rw [hbetween] at h
    simpa using h
  let step :=
    pair.toCrosscapBlockCommuteOfValid carrier
      carrierNegative insideTokens hbetween state.valid
  have stepInside : step.insideTokens = insideTokens := by
    exact pair.toCrosscapBlockCommuteOfValid_insideTokens carrier carrierNegative
      insideTokens hbetween state.valid
  have stepOutside :
      step.outsideTokens = pair.tailTokens := by
    exact pair.toCrosscapBlockCommuteOfValid_outsideTokens carrier carrierNegative
      insideTokens hbetween state.valid
  let execution :=
    step.commute state.separated state.classified
      state.protectedNodup state.valid
  let targetPair := step.targetPair residualInside
  refine
    { targetEdgeCount := n + 1
      targetTokens := step.targetTokens
      targetPair := targetPair
      targetState :=
        { valid := execution.targetValid
          separated := execution.targetSeparated
          classified := execution.targetClassified
          protectedNodup :=
            execution.targetProtectedNodup }
      targetProtectedNonempty := by
        simp [step, MarkedCrosscapBlockCommute.targetTokens,
          CompletedBlock.names]
      equivalent := execution.equivalent
      residualLengthEq := ?_
      rawBoundaryCountTailEq := by
        dsimp [targetPair,
          MarkedCrosscapBlockCommute.targetPair]
        rw [stepOutside]
        simp [ReductionToken.rawBoundaryCount]
      betweenLengthLt := ?_ }
  · rw [targetPair.residualDarts_length_eq,
      pair.residualDarts_length_eq]
    dsimp [targetPair,
      MarkedCrosscapBlockCommute.targetPair]
    simp [stepOutside, inverseWord_length]
  · rw [hbetween]
    dsimp [targetPair,
      MarkedCrosscapBlockCommute.targetPair]
    simp [stepInside]

end MarkedResidualCancellablePair
end Pairing
end WordReduction
end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
