@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedPhysicalData

open Set Function Filter ProblemStatement HarmonicCalculus LinearWaveBounds WeightedClasses

open scoped Topology ContDiff BigOperators InnerProductSpace

attribute [local instance] Classical.propDecidable

/-- An actual active label, retaining the native slot label and its band
bound without selecting data for omitted labels. -/
structure NativeLabel (active : Set PhysicalWaveSum.BandLabel) where
  /-- Val of `NativeLabel`, of type `SlotColoring.Label`. -/
  val : SlotColoring.Label
  property : 4 ≤ val.1
  mem : (⟨val, property⟩ : PhysicalWaveSum.BandLabel) ∈ active

end NavierStokes.ActualSignedPhysicalData
end
end
