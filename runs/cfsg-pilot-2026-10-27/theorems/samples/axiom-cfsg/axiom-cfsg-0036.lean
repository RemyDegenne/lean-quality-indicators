public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem F3.three_le_of_isCoverOf {Y : Type} [Group Y] {m p f : ℕ}
    (h : IsCoverOf .POmegaOdd m p f 2 Y) : 3 ≤ m := by
  obtain ⟨-, -, hm⟩ := h
  rcases hm with ⟨-, ⟨-, -, hn, -⟩, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact hn
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end CFSG.ComponentClassification.HarrisLit.T1
end
