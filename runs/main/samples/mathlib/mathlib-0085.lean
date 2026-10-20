@[expose] public section

open Set Filter TopologicalSpace

open scoped Topology

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

theorem Set.hasSeparatingCover_empty_left (s : Set X) : HasSeparatingCover ∅ s :=
  ⟨fun _ ↦ ∅, empty_subset (⋃ _, ∅),
   fun _ ↦ ⟨isOpen_empty, by simp only [closure_empty, empty_disjoint]⟩⟩

end Separation
end
