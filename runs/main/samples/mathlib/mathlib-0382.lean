@[expose] public section

noncomputable section

open Topology TopologicalSpace Filter Set

variable {X Y ι : Type*} {ι' : Sort*}

section IsGδ

variable [TopologicalSpace X]

theorem IsGδ.iUnion [Finite ι'] {f : ι' → Set X} (h : ∀ i, IsGδ (f i)) : IsGδ (⋃ i, f i) :=
  .sUnion (finite_range _) <| forall_mem_range.2 h

end IsGδ
end
end
