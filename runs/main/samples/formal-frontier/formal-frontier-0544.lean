open AlgebraicGeometry CategoryTheory

open scoped ProjectiveSpace LinearAlgebra.Projectivization

public section

noncomputable section

namespace ProjectiveSpace

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]

variable {ι : Type v} [Fintype ι]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι k

omit [IsAlgClosed k] in
theorem projectivizationToProj_injective :
    Function.Injective (projectivizationToProj (k := k) (ι := ι)) := by
  intro x y hxy
  induction x using Projectivization.ind with
  | h a ha =>
    induction y using Projectivization.ind with
    | h b hb =>
      change homogeneousCoordinatePoint a ha = homogeneousCoordinatePoint b hb at hxy
      obtain ⟨i, hbi⟩ : ∃ i, b i ≠ 0 := by
        by_contra h
        apply hb
        funext i
        simp only [not_exists, not_not] at h
        exact h i
      have hai : a i ≠ 0 := by
        rw [← homogeneousCoordinatePoint_mem_basicOpen_X_iff a ha i,
          hxy, homogeneousCoordinatePoint_mem_basicOpen_X_iff b hb i]
        exact hbi
      have hchart : affineCoordinatePoint a i = affineCoordinatePoint b i := by
        apply (standardCoordinateChartMap k ι i).isOpenEmbedding.injective
        rw [standardCoordinateChartMap_affineCoordinatePoint a ha i hai,
          standardCoordinateChartMap_affineCoordinatePoint b hb i hbi, hxy]
      have hnorm := normalizedCoordinates_eq_of_affineCoordinatePoint_eq a b i hchart
      rw [Projectivization.mk_eq_mk_iff' k]
      refine ⟨a i / b i, ?_⟩
      funext j
      by_cases hji : j = i
      · subst j
        simp [hbi]
      · have hj := congrFun hnorm ⟨j, hji⟩
        change a j / a i = b j / b i at hj
        change (a i / b i) * b j = a j
        field_simp at hj ⊢
        exact hj.symm

end ProjectiveSpace
end
end
