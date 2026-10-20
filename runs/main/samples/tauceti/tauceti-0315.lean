public section

namespace TauCeti.DynkinType.TypeB

variable {n : ℕ}

lemma shift_index {u v : Fin (2 * n)} (h : IsPair u v) :
    ((index u v).1 = u ∧ shift (index u v).1 (index u v).2 = v) ∨
      ((index u v).1 = v ∧ shift (index u v).1 (index u v).2 = u) := by
  rcases eq_or_ne u v with rfl | huv
  · have hlt : cyclicDistance u u < n := by
      rw [cyclicDistance_eq_zero_iff.mpr rfl]; exact rank_pos u
    exact Or.inl ⟨by rw [index, dite_eq_left hlt],
      by rw [index, dite_eq_left hlt]; exact shift_cyclicDistance hlt⟩
  obtain ⟨_, hn⟩ := h.cyclicDistance_ne huv
  have hsum := cyclicDistance_add_cyclicDistance huv
  by_cases h1 : cyclicDistance u v < n
  · exact Or.inl ⟨by rw [index, dite_eq_left h1],
      by rw [index, dite_eq_left h1]; exact shift_cyclicDistance h1⟩
  · have h2 : cyclicDistance v u < n := by omega
    exact Or.inr ⟨by rw [index, dite_eq_right h1, dite_eq_left h2],
      by rw [index, dite_eq_right h1, dite_eq_left h2]; exact shift_cyclicDistance h2⟩

end TauCeti.DynkinType.TypeB
end
