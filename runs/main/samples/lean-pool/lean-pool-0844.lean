@[expose] public section

open Metric Set

namespace Schoenflies

variable {γ : Type*} [Nonempty γ] {S₀ : CellStructure γ} {C : Set Plane}
  {P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}

theorem localGrid_frame_subset {p : Plane} {s : ℝ} {k : ℕ}
    (hs : 0 < s) (hk : 1 ≤ k) :
    Plane.closedSquare p s \ Plane.openSquare p s ⊆
      cover (localGridEdges p s k) := by
  intro z hz
  have hclosed := hz.1
  rw [Plane.closedSquare_eq_inter] at hclosed
  have hopen := hz.2
  rw [Plane.openSquare_eq_inter] at hopen
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hclosed
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, not_and_or, not_lt] at hopen
  rcases hopen with hX | hY
  · rcases hX with hleft | hright
    · exact mem_cover_of_coord_eq hs hk (Nat.zero_le k) hz.1 (by
        rw [localGridX_zero]
        linarith [hclosed.1.1])
    · exact mem_cover_of_coord_eq hs hk (le_refl k) hz.1 (by
        rw [localGridX_last hk]
        linarith [hclosed.1.2])
  · rcases hY with hbottom | htop
    · exact mem_cover_of_coord_eq' hs hk (Nat.zero_le k) hz.1 (by
        rw [localGridY_zero]
        linarith [hclosed.2.1])
    · exact mem_cover_of_coord_eq' hs hk (le_refl k) hz.1 (by
        rw [localGridY_last hk]
        linarith [hclosed.2.2])

end Schoenflies
end
