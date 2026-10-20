open scoped Finset

@[expose] public section

open Set Function

universe u v w x

variable {α : Type u} {β : Type v}

namespace Finset

section Preimage

theorem map_subset_iff_subset_preimage {f : α ↪ β} {s : Finset α} {t : Finset β} :
    s.map f ⊆ t ↔ s ⊆ t.preimage f f.injective.injOn := by
  classical rw [map_eq_image, image_subset_iff_subset_preimage]

end Preimage
end Finset
end
