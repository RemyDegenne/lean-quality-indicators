public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

section Transport3

theorem mem_map_subgroupOf_equiv_iff {G : Type*} [Group G] {Y : Subgroup G} (E : Subgroup G) (e : ↥Y ≃* UT3 F4)
    (g : ↥Y) : e g ∈ (E.subgroupOf Y).map e.toMonoidHom ↔ (g : G) ∈ E := by
  constructor
  · intro hg
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 hg
    have hcg : c = g := e.injective hce
    rw [hcg] at hc
    exact Subgroup.mem_subgroupOf.1 hc
  · intro hg
    exact Subgroup.mem_map.2 ⟨g, Subgroup.mem_subgroupOf.2 hg, rfl⟩

end Transport3
end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
end
