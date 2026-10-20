section

@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularDynamics

open Set Function Filter HarmonicCalculus

open CorrectionInitialization CorrectionState CorrectionStep

open ActualParticularStageControls CommonCoverSolve TorusInverse ParticularWaveBounds
    ParticularWaveAssembly

open scoped ContDiff Topology InnerProductSpace BigOperators

variable {B N0 : ℕ}

theorem cancellation_sum {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (N : ℕ) (Hs : SourceClasses x N α)
    (l : Label B N0) (S : ∀ j ∈ modes N, SupportData x l j)
    (hBand : (HarmonicResidual.residualBlock (assembly x l).context (assembly x l).state
      (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x
          l).aliasInput).BandLimited N)
    (n : ℕ) (z : (Parameter × TorusInverse.Plane) × ℝ) (hz : z.1 ∈ associatedStrip.domain) :
    (fun i => ∑ j ∈ modes N, ((actualWave x l j).harmonicResidual
      (ParticularParameters.nativeStrip associatedStrip) (directions (B := B)) n (angleShuffle z)
          i).re) +
      (HarmonicResidual.residualBlock (assembly x l).context (assembly x l).state
        (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x
            l).aliasInput).oscillation n z =
      (actualGood x l N).oscillation n z + (actualGaussian x l N).oscillation n z := by
  apply finite_cancellation (assembly x l).context (assembly x l).state (assembly x l).carrierBlock
    (assembly x l).gaussianInput (assembly x l).aliasInput N hBand
    (fun j n z => (actualWave x l j).harmonicResidual (ParticularParameters.nativeStrip
        associatedStrip)
      (directions (B := B)) n (angleShuffle z))
    (fun j n z => (data x l j).globalGood (ParticularParameters.nativeStrip associatedStrip)
      (directions (B := B)) n (angleShuffle (z,0)))
    (fun j n z => (data x l j).globalGaussian (directions (B := B)) n (angleShuffle (z,0))) n z
  intro j hj i
  exact section_equation Hc j ((mem_modes N j).mp hj).1 (Hs j hj) l (S j hj) n z hz i

end NavierStokes.ActualParticularDynamics
end
end
end
