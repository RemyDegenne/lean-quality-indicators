public section

namespace YoungDiagram

open Finset Nat

variable {μ : YoungDiagram} {r i j c : ℕ}

theorem image_betaNumber_sub_hookLength_union_image_betaNumber (hr : μ.colLen 0 ≤ r) :
    ((range (μ.rowLen i)).image fun c => μ.betaNumber r i - μ.hookLength (i, c)) ∪
        ((Ico (i + 1) r).image (μ.betaNumber r)) = range (μ.betaNumber r i) := by
  refine eq_of_subset_of_card_le ?_ ?_
  · intro m hm
    rcases mem_union.mp hm with hm | hm
    · obtain ⟨c, hc, rfl⟩ := mem_image.mp hm
      have hc' : c < μ.rowLen i := mem_range.mp hc
      have := hookLength_add_eq_betaNumber (colLen_le_of_colLen_zero_le hr c) hc'
      have := μ.hookLength_pos (c := (i, c))
      exact mem_range.mpr (by omega)
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
      obtain ⟨hj₁, hj₂⟩ := mem_Ico.mp hj
      exact mem_range.mpr (μ.betaNumber_lt_betaNumber hj₁ hj₂)
  · rw [card_union_of_disjoint (disjoint_image_betaNumber_sub_hookLength hr),
      card_image_of_injOn (strictMonoOn_betaNumber_sub_hookLength hr).injOn,
      card_image_of_injOn (μ.injOn_betaNumber_Ico r i),
      card_range, card_range, Nat.card_Ico, betaNumber_def]
    omega

end YoungDiagram
end
