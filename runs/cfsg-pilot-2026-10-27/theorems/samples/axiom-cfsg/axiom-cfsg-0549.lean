public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem false_of_wbar9_eq_top (S : SliceCore D L D₃ Y H) {E : Subgroup G}
    (hyp : F09.Hyp91 D Y H E) (hI : F09.I9 H ≤ D.M) (hW : wbar9 D Y H = ⊤) : False := by
  have hLM : F09.L9 Y H ≤ D.M := by
    intro l hl
    have hlH : l ∈ H := L9_le_of_le S.Y_le_H hl
    have hl' : (⟨l, hlH⟩ : ↥H) ∈ (F09.L9 Y H).subgroupOf H := Subgroup.mem_subgroupOf.2 hl
    have hmem : (⟨_, Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) hl'⟩ :
        F09.Lbar9 Y H) ∈ wbar9 D Y H := by
      rw [hW]
      exact Subgroup.mem_top _
    obtain ⟨g, hg, hgl⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hmem)
    have hgl' : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) g =
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) ⟨l, hlH⟩ := hgl
    obtain ⟨c, hc, hgc⟩ := (QuotientGroup.mk'_eq_mk' _).1 hgl'
    have hlc : l = (g : G) * (c : G) := by rw [← Subgroup.coe_mul, hgc]
    rw [hlc]
    exact D.M.mul_mem (Subgroup.mem_subgroupOf.1 hg).2 (hI (Subgroup.mem_map_of_mem H.subtype hc))
  exact S.not_H_le_M ((F09.eq_L9_sup_of_hyp91 hyp).le.trans (sup_le hLM inf_le_right))

end SliceCore
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
end
