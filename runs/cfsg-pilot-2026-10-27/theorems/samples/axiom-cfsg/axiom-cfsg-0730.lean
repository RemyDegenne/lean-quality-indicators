public section

namespace CFSG.QuasithinUnique.DoubleA3

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_zpowers_iff_of_sq_eq_one {z u : G} (hz : z ^ 2 = 1) :
    u ∈ Subgroup.zpowers z ↔ u = 1 ∨ u = z := by
  constructor
  · rintro ⟨k, rfl⟩
    show z ^ k = 1 ∨ z ^ k = z
    have h2 : z ^ (2 * (k / 2)) = 1 := by
      rw [zpow_mul]
      have : z ^ (2 : ℤ) = 1 := by exact_mod_cast hz
      rw [this, one_zpow]
    have hk' : k = 2 * (k / 2) + k % 2 := by omega
    have hk : z ^ k = z ^ (k % 2) := by
      conv_lhs => rw [hk']
      rw [zpow_add, h2, one_mul]
    rw [hk]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

end CFSG.QuasithinUnique.DoubleA3
end
