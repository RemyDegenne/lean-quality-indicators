public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem s11s_mem_pair {t t' d : G} (ht : t * t = 1) (ht' : t' * t' = 1)
    (hd : d ∈ zpowers t ⊔ zpowers t') : ∃ k : ℤ, d = (t' * t) ^ k ∨ d = (t' * t) ^ k * t := by
  have hd' : d ∈ Subgroup.closure ({t', t} : Set G) := by
    have hset : ({t', t} : Set G) = ({t} ∪ {t'} : Set G) := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure t,
      ← Subgroup.zpowers_eq_closure t']
    exact hd
  obtain ⟨k, hk | hk⟩ := s11s_mem_closure_pair_inv ht' ht hd'
  · exact ⟨k, Or.inl hk⟩
  · refine ⟨k + 1, Or.inr ?_⟩
    rw [hk, zpow_add_one, mul_assoc]
    congr 1
    rw [mul_assoc, ht, mul_one]

end CFSG.OddStandard.SmallF3.Omega
end
