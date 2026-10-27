public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] (L : Subgroup G)

theorem actsAs_one_iff [Group.IsPerfect ↥L] {g : G} :
    ActsAs L g (1 : MulAut (L ⧸ center L)) ↔ g ∈ centralizer (L : Set G) := by
  constructor
  · intro h
    obtain ⟨hg, hj⟩ := (actsAs_iff L).mp h
    have hker : (⟨g, hg⟩ : ↥(normalizer (L : Set G))) ∈ (jHom L).ker :=
      MonoidHom.mem_ker.mpr hj
    rw [ker_jHom] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  · intro hg
    have hgN : g ∈ normalizer (L : Set G) := Subgroup.centralizer_le_normalizer (L : Set G) hg
    refine (actsAs_iff L).mpr ⟨hgN, ?_⟩
    apply MonoidHom.mem_ker.mp
    rw [ker_jHom]
    exact Subgroup.mem_subgroupOf.mpr hg

end CFSG.OddStandard.HigherRank.YamadaG23
end
