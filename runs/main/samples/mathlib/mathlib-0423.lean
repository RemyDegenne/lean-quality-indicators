public section

open Function

variable {α β γ : Type*} {ι ι' ι₂ : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

namespace Set

theorem subset_iUnion₂_of_subset {s : Set α} {t : ∀ i, κ i → Set α} (i : ι) (j : κ i)
    (h : s ⊆ t i j) : s ⊆ ⋃ (i) (j), t i j :=
  le_iSup₂_of_le i j h

end Set
end
