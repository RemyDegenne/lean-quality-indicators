namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

lemma centralDistance_exceptional (L r : ℕ) (C D : Card r → Equiv.Perm (Card L))
    (E : Finset (Card r)) (h : ∀ u ∉ E, C u = D u) :
    centralDistance L r C D ≤ E.card*2^L := by
  classical
  calc
    _ ≤ ∑ u : Card r, if u ∈ E then 2^L else 0 := by
      apply Finset.sum_le_sum
      intro u _
      split_ifs with hu
      · simpa only [card_positions] using permDistance_le (C u) (D u)
      · rw [h u hu,permDistance_refl]
    _ = _ := by simp

end Thorp
end ThorpNine.Casimir
end OAI
