@[expose] public section

open Module Real Set Filter Bornology NNReal ENNReal WithLp

open scoped Uniformity

noncomputable section

namespace PiLp

variable (p : ℝ≥0∞) (𝕜 : Type*) {ι : Type*} (α : ι → Type*) (β : ι → Type*)

@[fun_prop, continuity]
theorem continuous_toLp [∀ i, TopologicalSpace (β i)] : Continuous (@toLp p (∀ i, β i)) :=
  continuous_induced_rng.2 continuous_id

end PiLp
end
end
