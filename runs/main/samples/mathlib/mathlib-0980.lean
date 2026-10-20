@[expose] public section

open Set Function Topology TopologicalSpace Relation

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section Preconnected

theorem IsPreconnected.iUnion_of_reflTransGen {ι : Type*} {s : ι → Set α}
    (H : ∀ i, IsPreconnected (s i))
    (K : ∀ i j, ReflTransGen (fun i j : ι => (s i ∩ s j).Nonempty) i j) :
    IsPreconnected (⋃ n, s n) := by
  rw [← biUnion_univ]
  exact IsPreconnected.biUnion_of_reflTransGen (fun i _ => H i) fun i _ j _ => by
    simpa [mem_univ] using K i j

end Preconnected
end
