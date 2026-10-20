public section

open Set

open scoped Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {s : Set α} [One β]

@[to_additive]
protected lemma Continuous.mulIndicator (hs : ∀ a ∈ frontier s, f a = 1) (hf : Continuous f) :
    Continuous (mulIndicator s f) := by
  classical exact hf.piecewise hs continuous_const

end
