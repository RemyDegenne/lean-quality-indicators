public section

open Equiv Function Finset

variable {α β : Type*}

namespace Equiv.Perm

section cycleFactors

open scoped List in
theorem list_cycles_perm_list_cycles {α : Type*} [Finite α] {l₁ l₂ : List (Perm α)}
    (h₀ : l₁.prod = l₂.prod) (h₁l₁ : ∀ σ : Perm α, σ ∈ l₁ → σ.IsCycle)
    (h₁l₂ : ∀ σ : Perm α, σ ∈ l₂ → σ.IsCycle) (h₂l₁ : l₁.Pairwise Disjoint)
    (h₂l₂ : l₂.Pairwise Disjoint) : l₁ ~ l₂ := by
  refine
    (List.perm_ext_iff_of_nodup (nodup_of_pairwise_disjoint_cycles h₁l₁ h₂l₁)
          (nodup_of_pairwise_disjoint_cycles h₁l₂ h₂l₂)).mpr
      fun σ => ?_
  by_cases hσ : σ.IsCycle
  · obtain _ := not_forall.mp (mt ext hσ.ne_one)
    rw [mem_list_cycles_iff h₁l₁ h₂l₁, mem_list_cycles_iff h₁l₂ h₂l₂, h₀]
  · exact iff_of_false (mt (h₁l₁ σ) hσ) (mt (h₁l₂ σ) hσ)

end cycleFactors
end Equiv.Perm
end
