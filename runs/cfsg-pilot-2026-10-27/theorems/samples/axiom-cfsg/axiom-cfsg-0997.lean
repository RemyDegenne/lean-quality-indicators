public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
  CFSG.LieType.BorelTits

open CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin.H13 (ModQ g2QAct g2QAct_injective G2NaturalCover G2DerivedNormalizerZorn
  card_ModQ)

variable {G : Type} [Group G]

section Canonical

set_option linter.unusedSectionVars false

theorem burnsideC137_caseU33
    : burnsideC137_CaseU33 := by
  intro G _ _ X T L P M V hyp hpsu
  obtain ⟨hXLT, hT, hL, hX, -, -, hTP, hPM, hM, hPeq, hred, hVL, -⟩ := hyp
  have hprod := burnsideC137_prod hXLT
  have hL2 := burnsideC137_charTwo_L hL hX
  have hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 := Or.inl ⟨by decide, hpsu⟩
  obtain ⟨hMX, hmax⟩ := burnsideC137_max hM
  have hP : P = M := hPeq.resolve_right fun h =>
    not_hatA6_of_psu33 hlie ⟨h.1.1.1, h.1.2.1, h.1.2.2⟩
  have hSQ : SQTKGroup ↥X :=
    c137SQTKSupply_holds G X T L hX hT hprod hL hL2 (Or.inr (Or.inr (Or.inr hlie)))
  obtain ⟨hredU, hUU, hCeq⟩ := u33_reduce hred hT hprod hL hlie hVL
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hUV : ⁅V, L⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hLX.trans hred.2.1)
  have cfg : U33Cfg X T ⁅V, L⁆ L P M :=
    ⟨hSQ, hX, hT, hprod, hL, hL2, hlie, hTP, hPM, hMX, hmax, hP, hredU, hUU, hVL⟩
  have hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32 :=
    MS93.MRes.asC132_of_descSp4 MS93.S4L.burnsideSp4H_s34RDescSp4
  rcases entry33_or_concl1
      (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
      asA21SQTKSection asA36NoOddCover_holds hX hSQ hredU hT hprod hL hL2 cfg.hVL' hlie
      cfg.toBaum.hQR cfg.toBaum.hRT with ⟨C, hC0, hCle, hCchar, hCn⟩ | E
  · exact Or.inl ⟨C, hC0, hCle, hCchar, hCn⟩
  · have hF := g2Facts_of_entry33 H13.VolI.g2NaturalCover_holds H13.g2DerivedNormalizerZorn
      u33G2Facts_holds E hUU
    rcases hF.dichotomy _ _ cfg.sylow_T cfg.T_le_P cfg.P_le_X cfg.P_ne_X cfg.P_max with hl | hp
    · exact Or.inr (Or.inr (Or.inr (Or.inl (burnsideC137_u33_concl4 cfg E hF
        H13.VolI.g2NaturalCover_holds H13.g2DerivedNormalizerZorn u33G2Facts_holds
        hred.2.2.1 hUV hred.2.1 hCeq hl))))
    · by_cases hcn : ∃ D : Subgroup G, D ≠ ⊥ ∧ D ≤ baum (pCoreOf 2 P) ∧
          (D.subgroupOf (baum (pCoreOf 2 P))).Characteristic ∧
          X ≤ Subgroup.normalizer (D : Set G)
      · exact Or.inl hcn
      · obtain ⟨A, hA, c, hc, hLc⟩ := hp.exists_PtA
        have hB := burnsideC137_u33_isG2Block cfg E hF hA hc hLc hC132
          fun C hCle hC0 hchar hXC => hcn ⟨C, hC0, hCle, hchar, hXC⟩
        refine Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr (burnsideC137_isG2TwoBlockNatural hB))),
          fun hH => ?_⟩)
        exact (not_hatA6_of_psu33 hlie ⟨hH.2.1.1.1, hH.2.1.2.1, hH.2.1.2.2⟩).elim

end Canonical
end CFSG.ASVolI
end
