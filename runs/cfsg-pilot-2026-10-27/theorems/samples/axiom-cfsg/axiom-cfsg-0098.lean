public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5

variable {G : Type} [Group G] [Finite G] {H T : Subgroup G} (M : Subgroup G)
  (hV : IsElemAbelian 2 (VZ T H))

variable {M} (hmin : MinParabolic H T M) (hmp : MinPar H T M) (hF : CharTwo H)
  (hred : IsTwoReducedIn H (VZ T H)) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G))

include hmin hmp hF hred hJ

theorem famI_basic :
    (famI M hV).Nonempty ∧
    autI hV (thompsonJ H) = ⨆ L ∈ famI M hV, L ∧
    (∀ L ∈ famI M hV, ∀ L' ∈ famI M hV, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
    (∀ L ∈ famI M hV, ∀ L' ∈ famI M hV, ∃ t ∈ autI hV T, B1.conjAut t L = L') := by
  have hF5 := fiveFive_of_e23 hV hmin hmp hF hred hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨E, hE⟩ := hF5.nonempty
    exact ⟨E, (mem_famI M hV).2 hE⟩
  · rw [autI_thompsonJ_eq_genD hV hmin hmp hF hred hJ, iSup_famI, hF5.iSup_eq]
  · intro L hL L' hL' hne a ha b hb
    exact hF5.comm L ((mem_famI M hV).1 hL) L' ((mem_famI M hV).1 hL') hne a ha b hb
  · intro L hL L' hL'
    obtain ⟨t, ht, htL⟩ := hF5.trans L ((mem_famI M hV).1 hL) L' ((mem_famI M hV).1 hL')
    refine ⟨t, ht, ?_⟩
    rw [← htL]
    ext x
    rw [B1.mem_conjAut, mem_conjSub_iff]

end CFSG.AGLEmbeddingD2.Tits.E23
end
