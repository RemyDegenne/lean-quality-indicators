@[expose] public section

noncomputable section

namespace NavierStokes.InitialPhysicalData

open Set Function Filter WeightedClasses HarmonicCalculus

open CorrectionInitialization ActualPrimaryBounds

open scoped Topology ContDiff BigOperators

attribute [local instance] Classical.propDecidable

section NativeCopies

variable {B N0 : ℕ}

theorem copyPotential_uniform :
    LabelSumBounds.UniformWaveClass fullStrip
      (fun i : SignedLabel B N0 × Frequency => fullEnvelope i.1) 1
      (fun i => copyPotentialCoefficient i.1 i.2) := by
  apply uniform_of_germ_or_zero (potentialCoefficient_uniform.reindex Prod.fst)
  intro i n x hx
  by_cases hk : nativeOfFull x ∈ (copyCells i.1).carrier n i.2
  · exact Or.inl (copyPotential_germ i.1 i.2 n hx hk)
  · exact Or.inr (copyPotential_zero_germ i.1 i.2 n hk)

end NativeCopies
end NavierStokes.InitialPhysicalData
end
end
