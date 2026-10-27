public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.Open Subgroup

theorem IsSpTwoLeviProduct.of_mulEquiv {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : IsSpTwoLeviProduct R) : IsSpTwoLeviProduct R' := by
  obtain ⟨k, X, hG, hF, ⟨e₀⟩, hX⟩ := h
  exact ⟨k, X, hG, hF,
    ⟨(QuotientGroup.congr (CFSG.pCore 2 R) (CFSG.pCore 2 R') e (CFSG.pCore_map_iso 2 e)).symm.trans
      e₀⟩, hX⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
end
