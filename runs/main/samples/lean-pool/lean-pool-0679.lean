@[expose] public section

noncomputable section

namespace NavierStokes.InitialPhysicalData

open Set Function Filter WeightedClasses HarmonicCalculus

open CorrectionInitialization ActualPrimaryBounds

open scoped Topology ContDiff BigOperators

attribute [local instance] Classical.propDecidable

section GlobalPrimaryPressure

variable {B N0 : ℕ}

theorem physicalPressure_periodic (l : SignedLabel B N0) (t r z : ℝ) :
    Periodic (fun θ => ActualPrimaryCoherence.physicalPressure l.1 l.2
      (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi) := by
  have hh := PhysicalParticularWave.mode_fullTurn
    (PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared l.1 l.2)
    (ActualPrimaryCoherence.physicalPhase_angular l.1 l.2)
    (physicalPressureCoefficient_invariant l) (one_mul _)
  intro θ
  change ActualPrimaryCoherence.physicalPressure l.1 l.2
      (t, AxisymmetricResidual.pack r (θ + 2 * Real.pi) z) =
    ActualPrimaryCoherence.physicalPressure l.1 l.2 (t, AxisymmetricResidual.pack r θ z)
  rw [physicalPressure_mode, physicalPressure_mode]
  apply congrArg Complex.re
  simpa only [ActualPrimaryCoherence.physicalAngular, PhysicalParticularWave.angle_translate_pack]
      using
    hh (t, AxisymmetricResidual.pack r θ z)

end GlobalPrimaryPressure
end NavierStokes.InitialPhysicalData
end
end
