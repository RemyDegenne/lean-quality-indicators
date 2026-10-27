public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

theorem lemma1315_of_inputs (h1314 : Lemma1314Statement)
    (hI2319 : Lemma1315b.Input23_19) (hI255 : Lemma1315b.Input25_5) (hI33 : Lemma1315b.Input3_3)
    (hI144 : Lemma1315b.Input14_4_1) (hI1418 : Lemma1315b.Input14_18)
    (hI1415 : Lemma1314.Input14_15) (hFi23 : Lemma1314.Input23_24Fi23)
    (hI112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2)
    (hI183 : Prop115.Input18_3Gen) (hDiag : Lemma1315b.Input18_3DiagZ)
    (hL2 : Lemma1315b.InputL2) : Lemma1315Statement := by
  have hI : Lemma1315b.Inputs :=
    ⟨hI2319, hI255, hI33, hI144, hI1418, hI1415, hFi23, hI112, hI183, hDiag, hL2⟩
  intro G _ _ m p B M E A D T R L0 d h h139a U hU hUR z H0 hz hH0 hH0M hH0t H
  obtain ⟨H', hH', tr, hs⟩ := Lemma1315b.exists_sit h1314 hI h h139a hU hUR hz hH0 hH0M hH0t
  subst hH'
  have h14 := h1314 h h139a
  have hIM := Lemma1315b.mem_normalizer_Iof h139a
  have hr : Lemma1315b.RIC p R (Iof p M D) :=
    ⟨fun r hr' => hIM r (hs.hb.rM hr'), h14.1.1, h14.1.2.1, h14.1.2.2⟩
  obtain ⟨P, -, -, -, -, -, -, -, -, -, -, -, hRB⟩ := hs.R_facts
  exact ⟨⟨tr.p57, tr.lp, tr.lq, hs.cyclic_centBar, tr.dN, tr.ninner⟩,
    Lemma1315.sylow_of_central_rank_two h hU.1 hUR, hRB,
    hs.iv hr (Lemma1315b.normalizer_R_le_M h hU.1 hUR) hIM⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
end
