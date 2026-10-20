section

@[expose] public section

noncomputable section

namespace NavierStokes.ActualValidBandWaves

open Set Filter Function ProblemStatement

open CorrectionInitialization CorrectionInitialization.ActualPrimary

open scoped Topology ContDiff BigOperators

variable {B N0 : ℕ}

section Incoming

variable {σ : ℝ} {x : CorrectionStep.CycleState (ActualInitialization.Index B N0)}
    {S : ActualInitialization.Index B N0 → ℕ → Set LocalSignedRequest.Point}
    (H : CorrectionStep.CycleAnalyticInvariant ActualInitialization.geometry (commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope S σ x)
    (C : ActualCycleCoherence.Coherent x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hS : ∀ l n, IsClosed (S l n))
    (hcore : ∀ l n, S l n ⊆ ActualCoreSupport.refinedCarrier l n)

include H

include hcore in
theorem refined_invariant : ActualParticularCycleData.Invariant σ x :=
  { H with inputSupport := fun l => ActualCycleAssembly.inputSupport_mono (H.inputSupport l) (hcore
      l) }

end Incoming
end NavierStokes.ActualValidBandWaves
end
end
end
