public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA CFSG.GH74.Exceptional

theorem cfgIRank_co2_three : CfgIRankRow 3 S8.Row.co2 := by
  unfold CfgIRankRow
  intro Q _ _ hcat hcard
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  have hbot : Subgroup.center Q = ⊥ := (Subgroup.eq_bot_iff_card _).2 hcard
  have hPSp : Nonempty (Q ⧸ Subgroup.center Q ≃* PSp43) := by
    rcases hi with hU | hB
    · exact CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_u4two ⟨i, hU, ⟨e⟩⟩
    · cases i with
      | cyclic p hp => exact False.elim hB
      | alternating n hn => exact False.elim hB
      | sporadic s => exact False.elim hB
      | lie idx =>
        obtain ⟨d, hd⟩ := idx
        obtain ⟨q, rfl, hq⟩ := exists_B2_of_onLie_three hB
        exact bridge_B2_three q hd hq e
  obtain ⟨e2⟩ := hPSp
  let f : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let φ : Q ≃* PSp43 := f.symm.trans e2
  obtain ⟨E, hE, hE27⟩ := transport_E27 φ CFSG.LocalAnalysis.GLTheoremA.CatB.U42.psp43_exists_E27
  refine ⟨E, hE, ?_⟩
  rw [hbot, inf_bot_eq, Subgroup.card_bot, hE27]
  norm_num [S8.Row.rank]

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI
end
