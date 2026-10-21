namespace OAI

open scoped BigOperators

namespace Balanced.PermutationSubsetLaw

variable {α : Type*} [DecidableEq α]

theorem exists_perm_fixing_map (S T : Finset α) (x : α)
    (hcard : S.card = T.card) (hxS : x ∉ S) (hxT : x ∉ T) :
    ∃ τ : Equiv.Perm α, τ x = x ∧ S.map τ.toEmbedding = T := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq S T hcard
  have hsx : σ x ∉ T := by
    intro h
    rw [← hσ] at h
    obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp h
    exact hxS ((σ.injective hzx) ▸ hz)
  have hswap : T.map (Equiv.swap (σ x) x).toEmbedding = T := by
    apply Finset.eq_of_subset_of_card_le _ (by simp)
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
    change Equiv.swap (σ x) x z ∈ T
    rw [Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hz hsx)
      (ne_of_mem_of_not_mem hz hxT)]
    exact hz
  refine ⟨σ.trans (Equiv.swap (σ x) x), by simp, ?_⟩
  change S.map (σ.toEmbedding.trans (Equiv.swap (σ x) x).toEmbedding) = T
  rw [← Finset.map_map, hσ, hswap]

end Balanced.PermutationSubsetLaw
end OAI
