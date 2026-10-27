public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33 (isLpType_of_mulEquiv
  card_of_isLpType_three_three exists_card_eq_three_pow sl_l33 su_l33_false
  isComponentOf_map_congr isLpType_center_map congr_self_eq exists_card_eq_pow_ringChar)

section SpCatalogue

open SymplecticHigher

theorem center_eq_bot_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

end SpCatalogue
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33c
end
