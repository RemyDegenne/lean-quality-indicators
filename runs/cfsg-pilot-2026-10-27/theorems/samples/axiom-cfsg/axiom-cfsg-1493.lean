public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

open CFSG.LargeExtraspecial.S4

open scoped commutatorElement

universe u

theorem eq_bot_of_normal_of_isPGroup_Gm {P : Subgroup Gm} (hn : P.Normal)
    (hp : IsPGroup 2 P) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro γ hγ
  rw [mem_bot]
  by_contra h1
  obtain ⟨δ, h3, hne⟩ := exists_mul_conj_pow_three γ h1
  have hx : γ * (δ * γ * δ⁻¹) ∈ P := mul_mem hγ (hn.conj_mem γ hγ δ)
  have h2 := hp.dvd_orderOf (g := ⟨_, hx⟩) fun h => hne (congrArg Subtype.val h)
  have h3' : orderOf (⟨_, hx⟩ : P) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [coe_pow]; exact h3))
  exact absurd (h2.trans h3') (by decide)

end CFSG.LargeExtraspecial.S10
end
