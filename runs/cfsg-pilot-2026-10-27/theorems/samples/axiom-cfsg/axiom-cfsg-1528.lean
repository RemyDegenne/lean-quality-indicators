public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Sporadic.Schreier.Tits (titsD card_titsD titsModelEquiv titsD_center)

open CFSG.SectionRank (exists_mulEquiv_titsGroup_of_model Tits_sylow3_cubic_witness)

open CFSG.AGLEmbeddingD2 (torusLocal_tits_sylow TorusLocal)

theorem normalizerMovesLines_of_torusLocal {p : ℕ} {X : Type} [Group X] {R : Subgroup X}
    (h : TorusLocal p R) : NormalizerMovesLines p R := by
  obtain ⟨-, -, -, -, t, ht, m, lam, e, hm, -, -, -, -, hlines⟩ := h
  intro A hAR hA
  refine ⟨t, ht, fun hmap => ?_⟩
  exact hlines 1 one_pos (by omega) A hAR hA
    (by rw [pow_one, Subgroup.mem_normalizer_iff_map_conj_eq]; exact hmap)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
end
