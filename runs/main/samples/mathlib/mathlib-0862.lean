public section

open Set Filter Topology

variable {α β : Type*} [TopologicalSpace α]

variable {f g : α → Set β} {s : Set α} {x : α}

section facts

variable [TopologicalSpace β]

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

variable {f g : α → Set β} {s : Set α} {x : α}

lemma UpperHemicontinuousAt.inter (hf : UpperHemicontinuousAt f x) {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuousAt (fun x ↦ f x ∩ u) x := by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hf.inter hu

end facts
end
