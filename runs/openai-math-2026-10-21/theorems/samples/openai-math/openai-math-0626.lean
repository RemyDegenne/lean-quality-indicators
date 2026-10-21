namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularSmallChains

variable {X : Type} [TopologicalSpace X]

@[simp] theorem mem_inSubset {s : Set X} {n : SimplexCategoryᵒᵖ}
    (σ : (singularSet X).obj n) :
    σ ∈ (inSubset s).obj n ↔
      Set.range (TopCat.toSSetObjEquiv (TopCat.of X) n σ) ⊆ s := by
  simp only [inSubset, Set.mem_ofPred_eq, Set.range_subset_iff]

end Problem340.SingularSmallChains
end
end OAI
