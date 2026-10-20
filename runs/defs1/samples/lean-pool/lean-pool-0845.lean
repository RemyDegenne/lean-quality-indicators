@[expose] public section

noncomputable section

namespace NavierStokes.PrimaryCopyBounds

open Set Function Filter PhaseJetBounds PrimaryPulseBounds WeightedClasses

open scoped Topology ContDiff BigOperators InnerProductSpace

variable {ι : Type*} {D : Type} {E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Actual full jets on varying native cells, retaining their full weight. -/
structure NativeJets (V : JetDomain ι D) (w : ι → D → ℝ) (f : ι → D → E) : Prop where
  nonneg : ∀ i x, x ∈ V.carrier i → 0 ≤ w i x
  smooth : ∀ i, ContDiffOn ℝ ∞ (f i) (V.carrier i)
  bound : ∀ m : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ i x, x ∈ V.carrier i → ∀ j ≤ m,
    ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C * V.growth i x ^ p * w i x

end NavierStokes.PrimaryCopyBounds
end
end
