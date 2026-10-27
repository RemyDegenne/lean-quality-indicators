public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint Subgroup

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem exists_v2_of_hyp1281One (h1222 : Stmt12_2_2) {T L V V₁ : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hV₁ : IsTSub T V V₁ 1) :
    ∃ V₂ : Subgroup G, IsTSub T V V₂ 2 ∧ V₁ ≤ V₂ := by
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hn : 2 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  exact exists_tsub_two_of_one h.hyp.sylow.1 hsq hab hTV hcard hn hV₁

end CFSG.Quasithin.H13
end
