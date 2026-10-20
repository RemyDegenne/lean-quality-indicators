public section

open Set Filter Function Filter

open scoped Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
  {f g : α → β} {s s' t : Set α} {x : α}

theorem ContinuousOn.piecewise' [∀ a, Decidable (a ∈ t)]
    (hpf : ∀ a ∈ s ∩ frontier t, Tendsto f (𝓝[s ∩ t] a) (𝓝 (piecewise t f g a)))
    (hpg : ∀ a ∈ s ∩ frontier t, Tendsto g (𝓝[s ∩ tᶜ] a) (𝓝 (piecewise t f g a)))
    (hf : ContinuousOn f <| s ∩ t) (hg : ContinuousOn g <| s ∩ tᶜ) :
    ContinuousOn (piecewise t f g) s :=
  hf.if' hpf hpg hg

end
