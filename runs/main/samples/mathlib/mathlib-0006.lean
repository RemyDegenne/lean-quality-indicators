@[expose] public section

open Function

variable {α β γ : Type*} {ι ι₂ : Sort*} {κ : ι → Sort*}

namespace Set

theorem subset_sUnion_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : t ⊆ ⋃₀ S :=
  le_sSup tS

end Set
end
