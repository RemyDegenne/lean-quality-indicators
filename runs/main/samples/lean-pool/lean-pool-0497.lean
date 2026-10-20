@[expose] public section

open Polynomial

namespace QuadraticIterates

section

variable (a : ℤ)

lemma isSquare_algebraMap_cSeq (n : ℕ) (hnsq : ¬IsSquare (-a : ℚ)) (m : ℕ) (hm1 : 1 ≤ m)
    (hmn : m ≤ n) :
    IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a m : ℚ)) := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : m ≠ 0)
  have hmono : splittingField a (k + 1) ≤ splittingField a n := splittingField_mono a hmn
  have hinj := (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)).injective
  have hsqrt (β : ↥((fℚ[a, k]).rootSet (AlgebraicClosure ℚ))) :
      ∃ γ : ↥(splittingField a n),
        (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) γ) ^ 2
          = (β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ) := by
    obtain ⟨δ, hδ⟩ := exists_sq_eq_sub a β
    have hroot : δ ∈ (fℚ[a, k + 1]).rootSet (AlgebraicClosure ℚ) :=
      (mem_rootSet_iteratedPoly_succ a k δ).mpr (by simp [hδ, sub_add_cancel, β.2])
    exact ⟨⟨δ, hmono (IntermediateField.subset_adjoin ℚ _ hroot)⟩, hδ⟩
  choose w hw using hsqrt
  have hnodup : ((fℚ[a, k]).aroots (AlgebraicClosure ℚ)).Nodup := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    · exact nodup_roots (irreducible_iteratedPoly_of_pos a hnsq hkpos).separable.map
  refine ⟨∏ β, w β, hinj ?_⟩
  have hlhs : algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)
      ((algebraMap ℚ (↥(splittingField a n))) (cSeq a (k + 1) : ℚ))
      = (cSeq a (k + 1) : AlgebraicClosure ℚ) := by
    simp
  rw [hlhs, map_mul, map_prod]
  have hsplit : (∏ β, algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (w β))
        * (∏ β, algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (w β))
      = ∏ β : ↥((fℚ[a, k]).rootSet (AlgebraicClosure ℚ)),
          ((β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun β _ ↦ by rw [← sq, hw β]
  rw [hsplit, prod_rootSet_eq_prod_aroots hnodup (· - (a : AlgebraicClosure ℚ))]
  exact (prod_aroots_sub_eq_cSeq a k).symm

end
end QuadraticIterates
end
