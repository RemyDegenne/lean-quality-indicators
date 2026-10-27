public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore

namespace CFSG.Combinatorics.HexagonLayers

variable {V : Type*}

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem dist_four_six (H : MooreHyp G) (col : G.Coloring Bool) {w x l a b : V}
    (hx : G.dist x w = 6) (hwl : G.Adj w l) (hal : G.Adj a l) (hbl : G.Adj b l) (hab : a ≠ b)
    (haw : a ≠ w) (hbw : b ≠ w) :
    (G.dist x a = 4 ∧ G.dist x b = 6) ∨ (G.dist x a = 6 ∧ G.dist x b = 4) := by
  have hl : G.dist x l = 4 + 1 := dist_eq_five_of_adj H col hx hwl
  have h46 : ∀ {t : V}, G.Adj t l → G.dist x t = 4 ∨ G.dist x t = 6 := by
    intro t ht
    rcases dist_adj H.conn col ht.symm x with h | h <;> omega
  rcases h46 hal with ha | ha <;> rcases h46 hbl with hb | hb
  · exact absurd (pred_unique H.cyc H.conn (by norm_num) hl hal.symm hbl.symm ha hb) hab
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact (not_three_far_on_line H col hx ha hb hwl hal hbl haw.symm hbw.symm hab).elim

end CFSG.Combinatorics.HexagonLayers
end
