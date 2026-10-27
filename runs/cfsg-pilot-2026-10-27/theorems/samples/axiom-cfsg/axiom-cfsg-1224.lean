public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec127_betaOf_eq_iff {V : Subgroup G} {m n : G} (hm : m ∈ normalizer (V : Set G))
    (hn : n ∈ normalizer (V : Set G)) :
    betaOf V m = betaOf V n ↔ m⁻¹ * n ∈ centralizer (V : Set G) := by
  have hmi : m⁻¹ ∈ normalizer (V : Set G) := (normalizer (V : Set G)).inv_mem hm
  rw [← sec127_betaOf_eq_one_iff ((normalizer (V : Set G)).mul_mem hmi hn),
    sec127_betaOf_mul hmi hn, sec127_betaOf_inv hm]
  exact inv_mul_eq_one.symm

end CFSG.OddStandard.SmallF3.Omega
end
