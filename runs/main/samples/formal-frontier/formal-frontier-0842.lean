public section

namespace GradedAlgebra

universe u v

variable {A : Type u} [CommRing A]

variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem finiteType_of_irrelevant_fg
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    Algebra.FiniteType (𝒜 0) A := by
  classical
  obtain ⟨s, hs, hhom⟩ := irrelevant_exists_finset_span_eq_of_fg 𝒜 h
  have hdegree : ∀ n (x : A), x ∈ 𝒜 n →
      x ∈ Algebra.adjoin (𝒜 0) (s : Set A) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hxn
      by_cases hn0 : n = 0
      · subst n
        exact Subalgebra.algebraMap_mem _ (⟨x, hxn⟩ : 𝒜 0)
      · have hxirr : x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
          HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 (Nat.pos_of_ne_zero hn0) hxn
        rw [← hs] at hxirr
        have hproj : ∀ y ∈ Ideal.span (s : Set A),
            ((DirectSum.decompose 𝒜 y) n : A) ∈ Algebra.adjoin (𝒜 0) (s : Set A) := by
          intro y hy
          induction hy using Submodule.closure_induction with
          | zero => simp
          | add y z _ _ hy hz =>
              rw [DirectSum.decompose_add]
              exact Subalgebra.add_mem _ hy hz
          | smul_mem a y hy =>
              obtain ⟨d, hd, hyd⟩ := hhom y hy
              rw [smul_eq_mul]
              by_cases hdn : d ≤ n
              · rw [DirectSum.coe_decompose_mul_of_right_mem_of_le 𝒜 hyd hdn]
                exact Subalgebra.mul_mem _
                  (ih (n - d) (Nat.sub_lt (Nat.pos_of_ne_zero hn0) hd) _
                    ((DirectSum.decompose 𝒜 a) (n - d)).2)
                  (Algebra.subset_adjoin hy)
              · rw [DirectSum.coe_decompose_mul_of_right_mem_of_not_le 𝒜 hyd hdn]
                exact Subalgebra.zero_mem _
        simpa [DirectSum.decompose_of_mem_same 𝒜 hxn] using hproj _ hxirr
  refine ⟨⟨s, ?_⟩⟩
  rw [← top_le_iff]
  intro x _
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Subalgebra.sum_mem _ fun n _ =>
    hdegree n _ ((DirectSum.decompose 𝒜 x) n).2

end GradedAlgebra
end
