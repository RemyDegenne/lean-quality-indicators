public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem isSylowTwoOf_top {X : Type} [Group X] {K S : Subgroup X}
    (h : IsSylowTwoOf S K) : IsSylowTwoOf (S.subgroupOf K) ⊤ := by
  refine ⟨le_top, h.2.1.comap_subtype, ?_⟩
  have : ((S.subgroupOf K).subgroupOf ⊤).index = (S.subgroupOf K).index := by
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  rw [this]
  exact h.2.2

end CFSG.Quasithin.Background.Harris.KFact2d
end
