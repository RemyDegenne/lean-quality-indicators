public section

namespace CFSG.RankThree.PartTwo.Sec4.Item419Res3

open CFSG CFSG.LocalCores

section Abstract

variable {C : Type*} [Group C]

theorem false_of_commutator_eq_bot {K H : Subgroup C} (hK : IsComponent K) (hKH : K ≤ H)
    (h : ⁅K, H⁆ = ⊥) : False := by
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
  have hbot : K = ⊥ := by
    rw [← hperf]
    exact le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hKH)
  have hnt := isQuasisimple_nontrivial hK.1
  exact ((Subgroup.nontrivial_iff_ne_bot K).mp hnt) hbot

end Abstract
end CFSG.RankThree.PartTwo.Sec4.Item419Res3
end
