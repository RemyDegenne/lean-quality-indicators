public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.SectionRank

namespace C129Native

theorem joinForm_of_minParabolicBlocks
    (hMB : MinParabolicBlocks)
    (hB113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat) (G : Type) [Group G] [Finite G] :
    JoinForm G := by
  intro X T M hX hSQ hT hT0 hcgs hMX
  have hTM : T ≤ M := fun t ht =>
    hcgs (inf_normalizer_le_cgsIn hT0 ⟨hT.1 ht, Subgroup.le_normalizer ht⟩)
  have h127 : L238.C127StatementCat (G := G) := L246C127.c127StatementCat_of_asB113 hB113
  have h123 : L238.C123TwoCgsStatement (G := G) := L246.C123.c123_holds G
  have hB42 : L238.AltBlockStatementJCat (G := G) := L238.altBlockStatementJCat_holds
  have hXq := Vol2Native.SQTKHypCat.quotient_pCore ↥X hSQ
  exact L238.lemma_C129_of_blocks h127 h123 hB42
    (L246A7.c129A7_of_inputs hMB h127 h123 hB42 a38ForSQTKCat_proved) hX hSQ
    (a38ForSQTKCat_proved _ hXq) (Vol2Native.a37ForSQTKCat_proved _ hXq) hT hT0 hcgs hMX
    (fun U hU hUM => L246A7.exists_block_of_mem_uFamHat_gen hMB hX hSQ hT hcgs hTM hU hUM)

end C129Native
end CFSG.Quasithin
end
