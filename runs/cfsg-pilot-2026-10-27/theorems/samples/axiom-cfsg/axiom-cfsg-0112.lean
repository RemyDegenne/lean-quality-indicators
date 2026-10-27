public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup

open scoped BigOperators

lemma inf_eq_bot_of_card_three_ne {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (hH : Nat.card H = 3) (hK : Nat.card K = 3) (hne : H ≠ K) : H ⊓ K = ⊥ := by
  classical
  by_contra hbot
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hyH : (y : G) ∈ H := (Subgroup.mem_inf.mp y.2).1
  have hyK : (y : G) ∈ K := (Subgroup.mem_inf.mp y.2).2
  have hyne : (y : G) ≠ 1 := by
    intro h
    exact hy1 (Subtype.ext h)
  have hdvdH : orderOf (y : G) ∣ 3 := by
    have h := Subgroup.orderOf_dvd_natCard H hyH
    rwa [hH] at h
  have ho3 : orderOf (y : G) = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdvdH with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hyne
    · exact h3
  have hzH : Subgroup.zpowers (y : G) = H := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyH) ?_
    rw [hH, Nat.card_zpowers, ho3]
  have hzK : Subgroup.zpowers (y : G) = K := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyK) ?_
    rw [hK, Nat.card_zpowers, ho3]
  exact hne (hzH.symm.trans hzK)

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
end
