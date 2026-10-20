public section

open Set Filter Function Topology

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ] {f g : α → β} {s s' s₁ t : Set α} {x : α}

theorem IsOpen.continuousOn_iff (hs : IsOpen s) :
    ContinuousOn f s ↔ ∀ ⦃a⦄, a ∈ s → ContinuousAt f a :=
  forall₂_congr fun _ => continuousWithinAt_iff_continuousAt ∘ hs.mem_nhds

end
