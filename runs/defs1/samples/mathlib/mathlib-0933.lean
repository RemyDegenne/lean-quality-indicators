@[expose] public section

open Bornology Set

variable {α : Type*} {s t : Set α}

section Lattice

variable [Lattice α] [Nonempty α]

/-- Order-bornology on a nonempty lattice. The bounded sets are the sets that are bounded both above
and below. -/
@[instance_reducible]
def orderBornology : Bornology α := .ofBounded
  {s | BddBelow s ∧ BddAbove s}
  (by simp)
  (fun _ hs _ hst ↦ ⟨hs.1.mono hst, hs.2.mono hst⟩)
  (fun _ hs _ ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩)
  (by simp)

end Lattice
end
