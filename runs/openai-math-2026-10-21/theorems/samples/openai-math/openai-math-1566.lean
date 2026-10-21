namespace OAI

open Set Metric MeasureTheory

open scoped NNReal ENNReal ContDiff BigOperators InnerProductSpace

noncomputable section

attribute [local instance] Classical.propDecidable

namespace RegularPointCoordinates

variable {X E F : Type*} [MetricSpace X]

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace IsLocalizedPatchCover

variable {A : Set X} {r : ℝ≥0} {u : X → E} {s : Finset X}
  {phi : X → E → ℝ} {N : ℕ} {C L : ℝ}

theorem one_le_cutoff_sum (d : IsLocalizedPatchCover A r u s phi N C L)
    {x : X} (hx : x ∈ A) : 1 ≤ ∑ y ∈ s, phi y (u x) := by
  obtain ⟨y, hy, _, hyone, _, _⟩ := d.weight_one_cover x hx
  calc
    1 = phi y (u x) := hyone.symm
    _ ≤ _ := Finset.single_le_sum (fun z _ => d.cutoff_nonneg z (u x)) hy

end IsLocalizedPatchCover
end Normed
end RegularPointCoordinates
end
end OAI
