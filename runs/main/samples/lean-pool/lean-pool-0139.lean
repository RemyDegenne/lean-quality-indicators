@[expose] public section

namespace SteinhausThreeGap

theorem posOrbit_nonempty (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    (posOrbit a N).Nonempty := by
  have hntriv : (orbit a N).Nontrivial := by
    rw [← Finset.one_lt_card_iff_nontrivial]
    exact lt_of_lt_of_le one_lt_two h2
  obtain ⟨x, hx, hx0⟩ := hntriv.exists_ne (0 : ℝ)
  exact ⟨x, by rw [mem_posOrbit_iff]; exact ⟨hx0, hx⟩⟩

end SteinhausThreeGap
end
