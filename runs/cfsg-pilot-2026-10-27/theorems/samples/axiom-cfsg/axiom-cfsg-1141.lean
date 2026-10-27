public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.Transvection

open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)

open CFSG.StronglyEmbedded.BenderCentre (benderRoot_pCoreOf_normalizer
  eq_sylowCenter_or_eq_of_normalized eq_conj_sylow eq_conj_sylowCenter
  not_mem_normalizer_of_not_commute sylow_sup_zpowers_eq_top mul_self_mem_sylowCenter)

variable {K : Type} [Group K] [Finite K] {A : Subgroup K}

theorem rootIrrAll_of_classical
    (h : ClassicalRootIrrStatement) : RootIrrAll := by
  intro K _ _ A hA
  rcases hA with hB | hC
  · exact benderRoot_irrModel hB
  · exact h K A hC

end CFSG.RankThree.GF2n.Tim79a
end
