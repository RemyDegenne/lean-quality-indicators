@[expose] public section

open Polynomial

namespace QuadraticIterates

scoped notation "fℚ[" a ", " n "]" => map (Int.castRingHom ℚ) (iteratedPoly a n)

section

variable (a : ℤ)

theorem kummer_degree_bound (n : ℕ) :
    splittingField a n ≤ splittingField a (n + 1) ∧
    (splittingField a (n + 1) = splittingField a n ⊔
      IntermediateField.adjoin ℚ
        ((fℚ[a, n + 1]).rootSet (AlgebraicClosure ℚ)) ∧
      ∀ β ∈ (fℚ[a, n + 1]).rootSet (AlgebraicClosure ℚ),
        β ^ 2 ∈ splittingField a n) ∧
    (splittingField a n).relfinrank (splittingField a (n + 1)) ≤ 2 ^ 2 ^ n := by
  have hmono := splittingField_le_succ a n
  refine ⟨hmono, ⟨(sup_eq_right.mpr hmono).symm, fun β hβ ↦ ?_⟩, relfinrank_succ_le a n⟩
  rw [← add_sub_cancel_right (β ^ 2) (a : AlgebraicClosure ℚ)]
  exact sub_mem
    (IntermediateField.subset_adjoin ℚ _ ((mem_rootSet_iteratedPoly_succ a n β).mp hβ))
    (IntermediateField.intCast_mem _ a)

end
end QuadraticIterates
end
