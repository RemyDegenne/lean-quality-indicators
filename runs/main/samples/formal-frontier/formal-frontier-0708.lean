@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace TopCat

theorem openSingularSet_inf {X : TopCat.{u}} (U V : Opens X) :
    openSingularSet U ⊓ openSingularSet V = openSingularSet (U ⊓ V) := by
  ext n x
  change (x ∈ (openSingularSet U).obj n ∧ x ∈ (openSingularSet V).obj n) ↔
    x ∈ (openSingularSet (U ⊓ V)).obj n
  rw [mem_openSingularSet_iff, mem_openSingularSet_iff,
    mem_openSingularSet_iff]
  simp only [Opens.coe_inf, Set.subset_inter_iff]

end TopCat
end
end
