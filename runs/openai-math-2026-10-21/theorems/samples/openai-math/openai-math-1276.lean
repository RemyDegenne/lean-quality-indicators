namespace OAI

namespace SeymourSecondNeighborhood.Extremal

open Pruning

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

theorem uncoveredZ_card_le (r : V → V → Prop) (R C P Q : Finset (V × V)) :
    (uncoveredZ r R C P Q).card ≤ uncoveredCount r P Q := by
  classical
  apply Finset.card_le_card
  intro z hz
  obtain ⟨_, hn⟩ := mem_uncoveredZ.mp hz
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, fun h =>
    hn (Finset.mem_union.mp h)⟩

end
end SeymourSecondNeighborhood.Extremal
end OAI
