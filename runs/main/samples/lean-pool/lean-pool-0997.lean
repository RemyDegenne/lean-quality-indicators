@[expose] public section

noncomputable section

open Set Filter Function

open scoped Topology ContDiff BigOperators

namespace NavierStokes.ActualParticularRealization

open HarmonicCalculus ParticularWaveAssembly ParticularWaveBounds

open CurlClassBounds hiding ComplexVector

open CorrectionState

section Assembly

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ)

open CopyAngularInvariance

theorem corrected_amplitude_invariant (j : ℤ)
    (B : BackgroundControl (CorrectionStep.ParticularParameters.nativeStrip s)
      D.directions D.background D.carrierBlock j) (n : ℕ) :
    Invariant (((0 : Parameter), (1 : ℝ)), (0 : Plane))
      ((corrected D s h gap j).amplitude n) := by
  have ha : Invariant D.directions.angular ((raw D h gap j).amplitude n) := by
    rw [B.angular]
    change Invariant _ (((CorrectionStep.ParticularParameters.fromReference D h gap).copyData
      D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j).common.amplitude n)
    rw [CorrectionStep.ParticularParameters.common_amplitude]
    exact angleLift_invariant _
  have hphi := actualCarrier_affine D.background D.carrierBlock j n
  rw [← B.angular] at hphi ⊢
  exact realizedCoefficient_invariant (B.radius_invariant n) (B.radial_invariant n)
    (Invariant.const _) (B.axial_invariant n) hphi ha ((j : ℝ) * D.carrierBlock.frequency n)

end Assembly
end NavierStokes.ActualParticularRealization
end
end
