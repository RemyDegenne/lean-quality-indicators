public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.EvenSporadicStandard

namespace Setting65

variable {Γ : Type} [Group Γ] {E H₁ : Subgroup Γ} {e : Γ} (hS : Setting65 Γ E H₁ e)

include hS

section Finite

variable [Finite Γ]

theorem normal_eq_or_eq_top {N : Subgroup Γ} [N.Normal] (hEN : E ≤ N) : N = E ∨ N = ⊤ := by
  have hnorm : ((N ⊓ H₁).subgroupOf H₁).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    exact Subgroup.normal_subgroupOf
  rcases hS.eq_or_eq_of_normal_le inf_le_right hnorm (inf_le_inf_right _ hEN) with h | h
  · exact Or.inl (hS.eq_E_of_inf_eq hEN h)
  · exact Or.inr (hS.eq_top_of_H₁_le hEN (inf_eq_right.1 h))

end Finite
end Setting65
end CFSG.EvenSporadicStandard.Induction.Balance
end
