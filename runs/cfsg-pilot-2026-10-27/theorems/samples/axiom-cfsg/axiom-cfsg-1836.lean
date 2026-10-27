public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

namespace Sec6SigOdd

section Groups

open CFSG.Open

open scoped Pointwise

section Basic

variable {G : Type*} [Group G]

theorem card_pairSub {u v : G} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (huv : u * v = v * u)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hne : u ≠ v) : Nat.card (pairSub u v hu hv huv) = 4 := by
  have huu : u * u = 1 := by simpa [pow_two] using hu
  have h1 : u * v ≠ 1 := fun h => hne (by
    have : v = u⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]; exact (inv_eq_of_mul_eq_one_right huu).symm)
  have h2 : u ≠ u * v := fun h => hv1 (by
    have := congrArg (fun w => u⁻¹ * w) h
    simpa using this.symm)
  have h3 : v ≠ u * v := fun h => hu1 (by
    have := congrArg (fun w => w * v⁻¹) h
    simpa using this.symm)
  have hc : Nat.card (pairSub u v hu hv huv) = ({1, u, v, u * v} : Set G).ncard :=
    Nat.card_coe_set_eq ({1, u, v, u * v} : Set G)
  rw [hc, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair h3]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, h2⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hu1.symm, hv1.symm, fun h => h1 h.symm⟩

end Basic
end Groups
end Sec6SigOdd
end CFSG.OddStandard.Solomon75
end
