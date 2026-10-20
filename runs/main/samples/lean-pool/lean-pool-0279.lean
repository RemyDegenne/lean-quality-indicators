@[expose] public section

noncomputable section

namespace NavierStokes.ActualCycleCoherence

open Set Function Filter CorrectionState CorrectionStep

open PhysicalResidualNaturality GaugeStateCoherence

open CorrectionInitialization CorrectionInitialization.ActualPrimary

open scoped ContDiff Topology BigOperators

section Step

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
  {S : Index B N0 → ℕ → Set Point}
  (H : CycleAnalyticInvariant ActualInitialization.geometry (commonContext B)
    ActualInitialization.tangentBlock ActualInitialization.envelope S σ x)
  (W : CorrectionAnalyticStep.WaveData ActualInitialization.geometry
    (ActualCycleParameters.fixedParameters B N0) x.coefficients (commonContext B) x.state
    ActualInitialization.envelope S σ ChartScales.kappa)

include H in
theorem source_fiber_continuous (hS : ∀ l n, IsClosed (S l n))
    (hpos : ∀ l n z, z ∈ ActualInitialization.geometry.domain → z ∈ S l n → 0 < z.1)
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (n : ℕ)
    (p : PhysicalParticularWave.Parameter) (hp : p.2 ∈ standardRegion.carrier) :
    Continuous (fun Y => particularSource x l j n (p,Y)) := by
  have hm : MapsTo (fun Y : PressureStream.Plane => (p,Y)) univ
      {z | z.1.2 ∈ standardRegion.carrier} := fun _ _ => hp
  exact continuousOn_univ.mp ((particularSource_smooth H hS hpos l j n).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hm)

end Step
end NavierStokes.ActualCycleCoherence
end
end
