public section

open Function Set

universe u

variable {α β γ δ : Type*} {ι ι' ι₂ : Sort*} {κ : ι → Sort*}

namespace Set

section Function

theorem image_iInter₂_subset (s : ∀ i, κ i → Set α) (f : α → β) :
    (f '' ⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), f '' s i j :=
  (mapsTo_iInter₂_iInter₂ fun i hi => mapsTo_image f (s i hi)).image_subset

end Function
end Set
end
