@[expose] public section

noncomputable section

namespace NavierStokes.PhysicalCopyBounds

open Set Function Filter ProblemStatement PhysicalWaveSum

open scoped Topology ContDiff BigOperators

variable {H Δ : ℕ} {K : Type*} {f : CopyFamily H K} {a b h r0 Z : ℝ}

section WeightedInputs

open WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {ι : Type*}

/-- The carrier profiles are estimated on their actual local slow regions.
The regions need contain a point only when that point belongs to this copy. -/
structure CarrierBounds (f : CopyFamily H K) (hc : SupportCells f) (a b h r0 : ℝ) where
  /-- Region of `CarrierBounds`, of type `K → BandLabel → Set PhysicalGraphBounds.Slow`. -/
  region : K → BandLabel → Set PhysicalGraphBounds.Slow
  open_region : ∀ k L, IsOpen (region k L)
  jets : PhaseJetBounds.PolynomialJets (copyBandDomain region open_region)
    (fun i x => ((f.carrier i.1 i.2).F x, (f.carrier i.1 i.2).G x))
  contains : ∀ k (I : WaveIndex H) z, z ∈ preterminal →
    physicalParams h z ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) z ∈ (hc.cells I.1).carrier I.1.val.1 k →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PolarCharts.chartDomain a chart →
    (PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
      (ChartScales.timeCoefficient h I.1.val.1) (f.carrier k I.1).center r0
      (PhysicalGraphBounds.physicalLift h I.1.val.1 z)).1 ∈ region k I.1

end WeightedInputs
end NavierStokes.PhysicalCopyBounds
end
end
