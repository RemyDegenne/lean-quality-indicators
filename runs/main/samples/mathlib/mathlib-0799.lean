public section

namespace IsNonarchimedean

variable {α β R : Type*} {a b : α} [LinearOrder R] {f : α → R} {n : ℕ}

theorem add_le [Semiring R] [IsStrictOrderedRing R] [Add α] (f_nonneg : ∀ x : α, 0 ≤ f x)
    (hna : IsNonarchimedean f) : f (a + b) ≤ f a + f b := by
  apply le_trans (hna _ _)
  rw [max_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
  exact ⟨f_nonneg _, f_nonneg _⟩

end IsNonarchimedean
end
