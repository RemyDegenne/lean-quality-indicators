@[expose] public section

namespace GenLimit.FiniteWitness.Anchored

theorem upper_valid (k : ℕ) : Valid (family k) (upperAssignment (k := k)) := by
  classical
  have hcross (i : Fin k) (D) (j : Fin k) (E) :
      ¬ ((↑(upperAssignment (k := k) (leftTarget i D)) : Set Point) ⊆ rightTarget j E ∧
        (↑(upperAssignment (k := k) (rightTarget j E)) : Set Point) ⊆ leftTarget i D) := by
    rintro ⟨hLR, hRL⟩
    by_cases h : j.val < (k + 1) / 2 ↔ i.val < (k + 1) / 2
    · have ha : Sum.inl j.val ∈ upperAssignment (k := k) (leftTarget i D) := by
        rw [upper_left, row_anchor]; exact h
      exact ((anchor_mem_right j j E).mp (hLR ha)) rfl
    · have ha : Sum.inr i.val ∈ upperAssignment (k := k) (rightTarget j E) := by
        rw [upper_right, col_anchor]; exact h
      exact ((anchor_mem_left i i D).mp (hRL ha)) rfl
  refine ⟨?_, ?_⟩
  · rintro L (⟨⟨i, D⟩, rfl⟩ | ⟨⟨j, E⟩, rfl⟩) x hx
    · rw [upper_left] at hx
      obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
      trivial
    · rw [upper_right] at hx
      obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
      trivial
  · intro S hS
    obtain ⟨L, hL⟩ := hS
    rcases hL.1 with ⟨⟨i, D⟩, rfl⟩ | ⟨⟨j, E⟩, rfl⟩
    · apply (Set.infinite_range_of_injective (Sum.inl_injective : Function.Injective
        (Sum.inl : ℕ → Point))).mono
      rintro _ ⟨n, rfl⟩ K hK
      rcases hK.1 with ⟨⟨j, E⟩, rfl⟩ | ⟨⟨j, E⟩, rfl⟩
      · trivial
      · exact (hcross i D j E ⟨fun x hx => hK.2.2 (hL.2.1 hx),
          fun x hx => hL.2.2 (hK.2.1 hx)⟩).elim
    · apply (Set.infinite_range_of_injective (Sum.inr_injective : Function.Injective
        (Sum.inr : ℕ → Point))).mono
      rintro _ ⟨n, rfl⟩ K hK
      rcases hK.1 with ⟨⟨i, D⟩, rfl⟩ | ⟨⟨i, D⟩, rfl⟩
      · exact (hcross i D j E ⟨fun x hx => hL.2.2 (hK.2.1 hx),
          fun x hx => hK.2.2 (hL.2.1 hx)⟩).elim
      · trivial

end GenLimit.FiniteWitness.Anchored
end
