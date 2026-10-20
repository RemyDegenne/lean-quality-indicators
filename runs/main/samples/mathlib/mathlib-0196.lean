@[expose] public section

open Function Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] (p n : ℕ) [ExpChar R p] (f : R[X])

open Multiset

theorem roots_expand_pow_map_iterateFrobenius_le :
    (expand R (p ^ n) f).roots.map (iterateFrobenius R p n) ≤ p ^ n • f.roots := by
  classical
  refine le_iff_count.2 fun r ↦ ?_
  by_cases h : ∃ s, r = s ^ p ^ n
  · obtain ⟨s, rfl⟩ := h
    simp_rw [count_nsmul, count_roots, ← rootMultiplicity_expand_pow, ← count_roots, count_map,
      count_eq_card_filter_eq]
    exact card_le_card (monotone_filter_right _ fun _ h ↦ iterateFrobenius_inj R p n h)
  convert Nat.zero_le _
  simp_rw [count_map, card_eq_zero]
  exact ext' fun t ↦ count_zero t ▸ count_filter_of_neg fun h' ↦ h ⟨t, h'⟩

end Polynomial
end
