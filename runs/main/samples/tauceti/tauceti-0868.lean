public section

namespace TauCeti

universe u v w

section Ring

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

theorem isSuperfluous_of_le_jacobson [IsCoatomic (Submodule R M)] {N : Submodule R M}
    (h : N ≤ Module.jacobson R M) : IsSuperfluous N := by
  intro K hK
  -- This is the nongenerating property of the order radical of a coatomic lattice.
  refine Order.radical_nongenerating (top_le_iff.mp ?_)
  rw [← hK, ← Module.jacobson_eq_radical]
  exact sup_le (le_sup_of_le_right h) le_sup_left

end Ring
end TauCeti
end
