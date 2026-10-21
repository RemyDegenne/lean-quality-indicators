namespace OAI

namespace PiExponent.GradedSerre

noncomputable section

open scoped BigOperators

variable {R M ι σ : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq ι] [SetLike σ M] [AddSubmonoidClass σ M]
  (𝓜 : ι → σ) [DirectSum.Decomposition 𝓜]

section IntegerGrading

variable {A P σA σP : Type*} [Ring A] [AddCommGroup P] [Module A P]
  [SetLike σA A] [AddSubgroupClass σA A]
  [SetLike σP P] [AddSubgroupClass σP P]
  (𝒜 : ℤ → σA) (𝓟 : ℤ → σP)
  [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition 𝓟]
  [SetLike.GradedSMul 𝒜 𝓟]

theorem free_cover_degree_compatible {J : Type*} [Fintype J]
    (w : J → ℤ) (v : J → P) (hv : ∀ j, v j ∈ 𝓟 (w j))
    (d : ℤ) (a : J → A) :
    Fintype.linearCombination A v
        (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w) a d : J → A) =
      (DirectSum.decompose 𝓟 (Fintype.linearCombination A v a) d : P) := by
  classical
  simp only [Fintype.linearCombination_apply, DirectSum.decompose_sum,
    DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ShiftedFreeGrading.decompose_apply]
  exact (decompose_smul_homogeneous 𝒜 𝓟 (hv j) (a j) d).symm

end IntegerGrading
end
end PiExponent.GradedSerre
end OAI
