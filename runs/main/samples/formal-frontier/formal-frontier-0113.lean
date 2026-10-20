@[expose] public section

open Filter

open scoped Pointwise Topology

universe u

namespace OpenSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

theorem exists_compact_subset_nhds_one [IsTopologicalGroup G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] {W : Set G} (hW : W ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ W := by
  have hT2 : T2Space G :=
    IsTopologicalGroup.t2Space_iff_one_closed.mpr isClosed_singleton
  obtain ⟨U, hUW, hUopen, hUone⟩ := mem_nhds_iff.mp hW
  obtain ⟨S, hScompact, hSone, hSU⟩ := exists_compact_subset hUopen hUone
  have hBasis : TopologicalSpace.IsTopologicalBasis {K : Set G | IsClopen K} :=
    @loc_compact_Haus_tot_disc_of_zero_dim G _ _ hT2 _
  obtain ⟨K, hKclopen, hKone, hKS⟩ :=
    hBasis.mem_nhds_iff.mp (isOpen_interior.mem_nhds hSone)
  have hKcompact : IsCompact K :=
    hScompact.of_isClosed_subset hKclopen.1 (hKS.trans interior_subset)
  obtain ⟨H, hHcompact, hHK⟩ :=
    exists_compact_subset_of_compact_open hKcompact hKclopen.2 hKone
  exact ⟨H, hHcompact, hHK.trans (hKS.trans (interior_subset.trans (hSU.trans hUW)))⟩

end OpenSubgroup
end
