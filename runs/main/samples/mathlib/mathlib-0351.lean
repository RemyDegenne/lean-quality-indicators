@[expose] public section

universe u v

variable {α : Type u} {β : Type v} {f : α → β} {M : Matroid α} {I J B B' X Y : Set α}

open Cardinal Set

namespace Matroid

section Rank

variable {κ : Cardinal}

theorem cRk_restrict_subset (M : Matroid α) (hYX : Y ⊆ X) : (M ↾ X).cRk Y = M.cRk Y := by
  have aux : ∀ ⦃I⦄, M.IsBasis' I Y ↔ (M ↾ X).IsBasis' I Y := by
    simp_rw [isBasis'_restrict_iff, inter_eq_self_of_subset_left hYX, iff_self_and]
    exact fun I h ↦ h.subset.trans hYX
  simp_rw [le_antisymm_iff, cRk_le_iff]
  exact ⟨fun I hI ↦ (aux.2 hI).cardinalMk_le_cRk, fun I hI ↦ (aux.1 hI).cardinalMk_le_cRk⟩

end Rank
end Matroid
end
