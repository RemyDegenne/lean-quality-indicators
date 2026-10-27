public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint

open CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem suz_fixedRootFree :
    SporadicFixedRootFree .Suz := by
  intro D _ _ hD hs n α S h
  obtain ⟨e⟩ := hs
  have := h.1
  by_cases hα : α ∈ inner D
  · refine h.false_of_inner_comps hD hα (isoInvariant_card_quotient_center {20160})
      (fun K _ _ hK h' => ?_) (fun t ht B hB => ?_)
    · rw [Set.mem_singleton_iff, card_sl2_quotient_center (by omega) hK] at h'
      have := lt_of_sl2Order_eq (by omega) (show 20160 < 2 ^ 15 by norm_num) h'
      interval_cases n <;> norm_num at h'
    · exact CFSG.Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e
        t ht B hB
  · rcases suz_outer_card e α h.2.1 hα with hcard | hcard
    · obtain ⟨hdvd, -, h2⟩ := h.two_pow_dvd (a := 7) (by rw [hcard]; norm_num)
      have h2 := h2 hα
      rw [hcard] at hdvd
      have := lt_of_sl2Order_dvd (by norm_num) (show 190080 < 2 ^ 18 by norm_num) hdvd
      interval_cases n <;> revert hdvd h2 <;> norm_num
    · obtain ⟨hdvd, -, h2⟩ := h.two_pow_dvd (a := 8) (by rw [hcard]; norm_num)
      have h2 := h2 hα
      rw [hcard] at hdvd
      have := lt_of_sl2Order_dvd (by norm_num) (show 1209600 < 2 ^ 21 by norm_num) hdvd
      interval_cases n <;> revert hdvd h2 <;> norm_num

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
end
