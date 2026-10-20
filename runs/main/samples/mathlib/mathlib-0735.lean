@[expose] public section

open Function

variable {α β γ : Type*} {ι ι₂ : Sort*} {κ : ι → Sort*}

namespace Set

theorem iInter₂_eq_empty_iff {s : ∀ i, κ i → Set α} :
    ⋂ (i) (j), s i j = ∅ ↔ ∀ a, ∃ i j, a ∉ s i j := by
  simp only [eq_empty_iff_forall_notMem, mem_iInter, not_forall]

end Set
end
