public section

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*} {κ : ι → Sort*}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {a b : α}

@[to_dual self (reorder := hf hf')]
lemma ciInf_le_ciSup [Nonempty ι] {f : ι → α} (hf : BddBelow (range f)) (hf' : BddAbove (range f)) :
    ⨅ i, f i ≤ ⨆ i, f i :=
  (ciInf_le hf (Classical.arbitrary _)).trans <| le_ciSup hf' (Classical.arbitrary _)

end ConditionallyCompleteLattice
end
