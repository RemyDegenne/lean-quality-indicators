@[expose] public section

set_option warningAsError true

namespace ProfiniteGrp.CompatibleSubgroups

variable (G : ProfiniteGrp)

theorem map_reconstruct (S : Family G) (hS : Compatible G S)
    (U : OpenNormalSubgroup G) :
    (reconstruct G S).map (QuotientGroup.mk' U.toSubgroup) = S U := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr (iInf_le _ U)
  · intro a ha
    let B : Set G := (QuotientGroup.mk' U.toSubgroup) ⁻¹' ({a} : Set (G ⧸ U.toSubgroup))
    let C (V : OpenNormalSubgroup G) : Set G :=
      (QuotientGroup.mk' V.toSubgroup) ⁻¹' (S V : Set (G ⧸ V.toSubgroup))
    have hB : IsCompact B := by
      have : DiscreteTopology (G ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
      exact (IsClosed.preimage (QuotientGroup.continuous_mk (N := U.toSubgroup))
        (isClosed_discrete ({a} : Set (G ⧸ U.toSubgroup)))).isCompact
    have hC (V : OpenNormalSubgroup G) : IsClosed (C V) := by
      change IsClosed ((S V).comap (QuotientGroup.mk' V.toSubgroup) : Set G)
      exact coordinate_closed G S V
    have hfinite (F : Finset (OpenNormalSubgroup G)) :
        (B ∩ ⋂ V ∈ F, C V).Nonempty := by
      obtain ⟨W, hWU, hWF⟩ := common_refinement G U F
      have haW : a ∈ (S W).map (transition G W U hWU) := by
        rw [hS hWU]
        exact ha
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp haW
      obtain ⟨g, hgb⟩ := QuotientGroup.mk'_surjective W.toSubgroup b
      refine ⟨g, ?_, ?_⟩
      · change QuotientGroup.mk' U.toSubgroup g = a
        calc
          QuotientGroup.mk' U.toSubgroup g =
              transition G W U hWU (QuotientGroup.mk' W.toSubgroup g) :=
            (transition_mk G W U hWU g).symm
          _ = transition G W U hWU b := by rw [hgb]
          _ = a := hba
      · simp only [Set.mem_iInter]
        intro V hVF
        change QuotientGroup.mk' V.toSubgroup g ∈ S V
        rw [← hS (hWF V hVF), ← transition_mk G W V (hWF V hVF), hgb]
        exact Subgroup.mem_map_of_mem _ hb
    obtain ⟨g, hgB, hgC⟩ := hB.inter_iInter_nonempty C hC hfinite
    apply Subgroup.mem_map.mpr
    refine ⟨g, ?_, hgB⟩
    change g ∈ ⨅ V : OpenNormalSubgroup G,
      (S V).comap (QuotientGroup.mk' V.toSubgroup)
    exact Subgroup.mem_iInf.mpr (fun V => Set.mem_iInter.mp hgC V)

end ProfiniteGrp.CompatibleSubgroups
end
