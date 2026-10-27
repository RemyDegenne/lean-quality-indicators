@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularStageControls

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryPulseBounds

open CorrectionState CorrectionStep CommonCoverSolve TorusInverse

open scoped ContDiff Topology BigOperators

open CorrectionInitialization CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ}

/-- Signed phase, bundling `epsilon`, `p`, `pz`, `x0` and the required compatibility proofs. -/
noncomputable def signedPhase {ι : Type} {D : Domain ι Slow}
    (F : Fin 2 → PhaseConstruction D) : PhaseFamily (Fin 2 × ι) where
  epsilon l := (F l.1).phase.epsilon l.2
  p l := (F l.1).phase.p l.2
  pz l := (F l.1).phase.pz l.2
  x0 l := (F l.1).phase.x0 l.2
  theta l := (F l.1).phase.theta l.2
  F l := (F l.1).phase.F l.2
  G l := (F l.1).phase.G l.2

end NavierStokes.ActualParticularStageControls
end
end
