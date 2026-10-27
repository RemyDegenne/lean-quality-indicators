public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G]

theorem exists_five_part {W : Subgroup G} (hW : IsPGroup 2 W) {x : G} (hx5 : x ^ 5 ∈ W)
    (hxW : x ∉ W) : ∃ n : ℕ, orderOf (x ^ n) = 5 ∧ x ^ n * x⁻¹ ∈ W := by
  refine exists_five_part_of_coprime hx5 hxW ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hW ⟨x ^ 5, hx5⟩
  have h2 : orderOf (x ^ 5) = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (⟨x ^ 5, hx5⟩ : W)
  rw [h2]
  exact Nat.Coprime.pow_left k (by norm_num)

end SBc17
end CFSG.Quasithin
end
