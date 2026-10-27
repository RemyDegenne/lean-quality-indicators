public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16h_mParam_le_two_of_Z3_six_two (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) 3)
    (hrk : rk ↥(wTil V₀ V h.hyp151.isElemAbelian L) = 6)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2) (h3 : D.sig = {3}) :
    E3.mParam (Mbar D.M V₀ V h.hyp151.isElemAbelian) ≤ 2 := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp16.hyp125.pairFacts.le_normalizer h.hyp16.hyp125.pairFacts.le_normalizer₀
  have hp3 : (3 : ℕ).Prime := by norm_num
  have hk : D.k = 1 := by
    have hsp := S.hSig.sig1_sp 3 (by rw [← hσ, h3]; exact Set.mem_singleton 3)
    unfold Data.k RankThreeUC.kParam
    rw [if_pos hsp]
  have hodd : Odd (Nat.card ↥(lBar V₀ V h.hyp151.isElemAbelian L)) := by rw [hLp.2]; norm_num
  have hfix : wTil V₀ V h.hyp151.isElemAbelian L ⊓
      fixV (lBar V₀ V h.hyp151.isElemAbelian L) = ⊥ :=
    s16c167_wTil_inf_fixV_eq_bot_of_odd h.hyp151.isElemAbelian L hodd
  obtain ⟨t, htM, ht2, ht1, htr, hW⟩ := hc
  obtain ⟨-, -, -, hLt, hind, -⟩ := s16h_conc4_133_of_prime_card hp3 hLp.2 hW
  have hT : IsSylowIn 2 (barSub V₀ V h.hyp151.isElemAbelian D.T)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian) := by
    have hT0 := s16c7_isSylowOf_barSub (p := 2) V₀ V h.hyp151.isElemAbelian D.sylowM hMs
    rwa [CFSG.ABGLocalTools.isSylowOf_iff] at hT0
  obtain ⟨Xb, hXn, hXe, hXd, hXc, hirr⟩ :=
    s16h_z3_exists_xbar_irr (fun w => s15_Infra_vtil_sq_eq_one V₀ V h.hyp151.isElemAbelian w)
      hW hind hs hLp.2 hrk hfix htM ht2 htr hLt hT
  have hNot := s16h_not_mBarGT_of_bar_two D S.hSig S.h61 S.h63 S.h77 S.h869 S.h111 S.h112
    S.hThin S.hCyc S.h127 S.h126 S.h1211 S.h111W S.h6161ii hσ h.hyp16 hp3 (by norm_num)
    hXn hXe hXd hXc hirr
  have hNot2 : ¬ MBarGT D.M V₀ V 2 := by simpa [hk] using hNot
  have hmle : mBar D.M V₀ V h.hyp151.isElemAbelian ≤ 2 :=
    not_lt.1 fun hlt => hNot2 ((h.hyp151.hyp125.mBarGT_iff_lt_mBar 2).2 hlt)
  exact hmle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
