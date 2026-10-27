public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional

open CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ComponentClassification.RankTwoStandard

open scoped Pointwise

namespace G2

variable {K : Type} [Field K] [CharP K 2]

theorem ringEquiv_apply_apply [Finite K] (hK : Nat.card K = 4) (σ : K ≃+* K) (t : K) :
    σ (σ t) = t := by
  by_cases h0 : t = 0
  · rw [h0, map_zero, map_zero]
  by_cases h1 : t = 1
  · rw [h1, map_one, map_one]
  have ht := sq_add_self_add_one_of_ne hK h0 h1
  have hst : σ t ^ 2 + σ t + 1 = 0 := by
    have h := congrArg σ ht
    rwa [map_add, map_add, map_pow, map_one, map_zero] at h
  have hprod : (σ t + t) * (σ t + t + 1) = 0 := by
    linear_combination (norm := char2_ring) hst + ht
  rcases mul_eq_zero.mp hprod with h | h
  · have h' : σ t = t := by linear_combination (norm := char2_ring) h
    rw [h', h']
  · have h' : σ t = t + 1 := by linear_combination (norm := char2_ring) h
    rw [h', map_add, map_one, h']
    linear_combination (norm := char2_ring)

end G2
end CFSG.ComponentClassification.AS81
end
