public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem lemma15128InputU_of_named_inputs (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (nTr : Input15128OffenderTransfer) (nML : Input15128ML)
    (nN : Input15128Natural) (nS : Input15128SumNatDual) : Lemma15128InputU := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 h25 h26 h27
  have hc : Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L := ⟨hC, h17, h18, h19, hL, h22, h24, h25, h26, h27⟩
  have hoff := offender15128_of hC27 nTr G T Mc M Z₁ Z₂ V₁ V₂ L hc
  by_cases hsum : SumNatDual15127 Z₂ L
  · exact (nS G T Mc M Z₁ Z₂ V₁ V₂ L hc hsum hoff).elim
  · obtain ⟨hML1, hML2⟩ := nML G T Mc M Z₁ Z₂ V₁ V₂ L hc hsum
    obtain ⟨hnat, hcard⟩ := nN G T Mc M Z₁ Z₂ V₁ V₂ L hc hsum hML2 hoff
    exact ⟨hnat, hcard, hML1, hML2⟩

end CFSG.Quasithin
end
