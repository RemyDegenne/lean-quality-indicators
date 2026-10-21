namespace OAI

namespace LowSpaceSubsetSum

open scoped BigOperators

universe u v w

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem representativeCategories_disjoint {D A M : Finset ι} (hDA : D ⊆ A) :
    ∀ i j, i ≠ j → Disjoint (representativeCategories D A M i)
      (representativeCategories D A M j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hdx : x ∈ D → x ∈ A := fun hx => hDA hx
  fin_cases i <;> fin_cases j <;> simp_all [representativeCategories]

end LowSpaceSubsetSum
end OAI
