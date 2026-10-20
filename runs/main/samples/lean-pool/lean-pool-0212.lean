@[expose] public section

namespace NavierStokes.PhysicalParticularWave

open Set Filter Function ProblemStatement HarmonicCalculus

open ParticularWaveAssembly ParticularWaveBounds LinearWaveBounds WeightedClasses

open CommonCoverSolve TorusInverse CopyAngularInvariance

open scoped ContDiff Topology

noncomputable section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem bandPressureMode_eq_physical (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (i gap : ℕ) {K : ℝ} (hK : K ≠ 0) (j : ℤ)
    (hKr : referenceFrequency D j ≠ 0) {U : Set Parameter} (R : ReferenceODE D j U)
    {z : SpaceTime} (hz : 0 < z.2 0)
    (hp : parameterChange h Q Qr (nativeMap h Q i z).1.1 ∈ U) :
    bandPressureMode D h hQ hQr gap K j ((PhysicalResidualBridge.commonGraph Q h i).map z) =
      (Q ^ (2 * CoordinateAlgebra.A h) : ℝ) • complexPhysicalPressure D h Qr (i + gap) j z := by
  have hraw := bandRawPressure_eq_lift D h hQ hQr gap hK j hKr R
    ((PhysicalResidualBridge.commonGraph Q h i).map z) hp
  rw [cylinderChange_graph hQ hQr h i gap hz] at hraw
  have hc : carrier K (bandPhase D h Q Qr gap K j) ((PhysicalResidualBridge.commonGraph Q h i).map
      z) =
      carrier (referenceFrequency D j) (physicalPhase D h Qr (i + gap) j) z := by
    apply PhysicalCurlCovariance.carrier_eq_of_products
    change K * ((referenceFrequency D j / K) * liftPhase D j
      (cylinderChange h Q Qr gap ((PhysicalResidualBridge.commonGraph Q h i).map z))) =
      referenceFrequency D j * liftPhase D j ((PhysicalResidualBridge.commonGraph Qr h (i +
          gap)).map z)
    rw [cylinderChange_graph hQ hQr h i gap hz]
    field_simp
  have hw : pressureWeight h Q Qr = Q ^ (2 * CoordinateAlgebra.A h) * Qr ^ (-(2 *
      CoordinateAlgebra.A h)) := by
    unfold pressureWeight ratioPower
    rw [Real.rpow_neg hQr.le, div_eq_mul_inv]
  unfold bandPressureMode complexPhysicalPressure HarmonicCalculus.mode
  rw [hraw, hc, hw]
  simp only [physicalPressureCoefficient, Complex.real_smul, Complex.ofReal_mul, nativeMap]
  ring

end
end NavierStokes.PhysicalParticularWave
end
