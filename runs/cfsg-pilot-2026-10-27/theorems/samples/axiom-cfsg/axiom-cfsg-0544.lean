public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

theorem m12_fixSub_card
    (w : MulAut ↥CFSG.Blueprint.NativeSporadic.M12) (hw : orderOf w = 2) :
    ¬ 9 ∣ Nat.card ↥(CFSG.Sporadic.Schreier.fixSub w) := by
  by_cases hin : w ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥CFSG.Blueprint.NativeSporadic.M12
  · refine fixSub_card_inner CFSG.Sporadic.Schreier.m12_center_eq_bot' (fun u hu => ?_) w hw hin
    rw [← card_centralizerIn_eq]
    exact m12_inner_card u.1 u.2 (by rw [Subgroup.orderOf_coe]; exact hu)
  · have hw2 : w * w = 1 := by
      rw [← sq]
      have := pow_orderOf_eq_one w
      rwa [hw] at this
    set e := CFSG.Sporadic.Schreier.m12EquivD with he
    have hw'2 : MulAut.congr e w * MulAut.congr e w = 1 := by
      rw [← map_mul, hw2, map_one]
    have hw'out : MulAut.congr e w ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥CFSG.Sporadic.Schreier.m12D.originalSubgroup := by
      intro h
      apply hin
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at h
      obtain ⟨β, hβ, hβα⟩ := h
      rwa [(MulAut.congr e).injective hβα] at hβ
    have key := fixSub_card_outer CFSG.Sporadic.Schreier.m12D.originalSubgroup
      CFSG.Sporadic.Schreier.m12Sigma CFSG.Sporadic.Schreier.m12D_sigma_normalizes
      CFSG.Sporadic.Schreier.m12D_sigma_sq CFSG.Sporadic.Schreier.m12D_center
      CFSG.Sporadic.Schreier.m12D_sigma_outer CFSG.Sporadic.Schreier.m12D_mulAut_card
      m12D_outer_card (MulAut.congr e w) hw'2 hw'out
    rwa [← CFSG.Sporadic.Schreier.map_fixSub_equiv e w,
      Subgroup.card_map_of_injective e.injective] at key

end CFSG.LocalAnalysis.GLTheoremA.CatB
end
