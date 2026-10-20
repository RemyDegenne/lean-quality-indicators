public section

open Polynomial NumberField Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

variable {θ : 𝓞 K} {d : ℤ}

theorem adjoin_rat_halfGen_eq_top (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hd4 : d % 4 = 1) :
    Algebra.adjoin ℚ {(halfGen hmin hd4 : K)} = ⊤ := by
  rw [eq_top_iff, ← hgen, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
  have hθ : (θ : K) = 2 * (halfGen hmin hd4 : K) - 1 := by rw [coe_halfGen]; ring
  rw [hθ]
  exact sub_mem (mul_mem (ofNat_mem _ 2) (Algebra.subset_adjoin (Set.mem_singleton _))) (one_mem _)

end NumberField
end
