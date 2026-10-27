@[expose] public section

noncomputable section

namespace NavierStokes.ActualReferenceRebase

open Set Function Filter WeightedClasses CorrectionState HarmonicFields HarmonicCalculus

open CommonCoverSolve TorusInverse PhysicalParticularWave

open scoped ContDiff Topology BigOperators ComplexConjugate

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

open CorrectionInitialization CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ}

/-- Native assembly, given by `rebaseAssembly (ActualParticularStageControls.assembly x l)
(ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2))`. -/
noncomputable def nativeAssembly
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) : ParticularWaveAssembly.AssemblyData Parameter
        :=
  rebaseAssembly (ActualParticularStageControls.assembly x l)
    (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2))

end NavierStokes.ActualReferenceRebase
end
end
