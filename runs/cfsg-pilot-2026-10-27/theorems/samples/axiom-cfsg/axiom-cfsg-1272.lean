public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin
  CFSG.Quasithin.F53Push CFSG.ABGLocalTools Subgroup

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem e9_le_of_normal {O N S : Subgroup G} (hNO : N ≤ O) (hNn : O ≤ normalizer (N : Set G))
    (hN2 : IsPGroup 2 N) (hS : IsSylowOf 2 S O) : N ≤ S := by
  obtain ⟨Q, hQ⟩ := hS
  have hnorm : (N.subgroupOf O).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNO).mpr hNn
  have hp : IsPGroup 2 (N.subgroupOf O) := hN2.comap_subtype
  have hle : N.subgroupOf O ≤ (Q : Subgroup O) := hp.le_sylow_of_normal Q
  intro g hg
  have hg' : (⟨g, hNO hg⟩ : O) ∈ N.subgroupOf O := hg
  rw [← hQ]
  exact ⟨⟨g, hNO hg⟩, hle hg', rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
end
