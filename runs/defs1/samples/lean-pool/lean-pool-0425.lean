@[expose] public section

namespace TauCeti

open TauCeti

open scoped InnerProductSpace BigOperators ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The real-linear rotation by `theta` on two copies of a real vector space. -/
noncomputable def realRotationLinearEquiv
    {G : Type*} [AddCommGroup G] [Module ℝ G]
    (theta : ℝ) : (G × G) ≃ₗ[ℝ] (G × G) where
  toFun x :=
    (Real.cos theta • x.1 - Real.sin theta • x.2,
      Real.sin theta • x.1 + Real.cos theta • x.2)
  invFun x :=
    (Real.cos theta • x.1 + Real.sin theta • x.2,
      -Real.sin theta • x.1 + Real.cos theta • x.2)
  left_inv x := by
    have htrig := cos_mul_cos_add_sin_mul_sin theta
    apply Prod.ext <;> dsimp
    · conv_rhs => rw [← one_smul ℝ x.1, ← htrig]
      module
    · conv_rhs => rw [← one_smul ℝ x.2, ← htrig]
      module
  right_inv x := by
    have htrig := cos_mul_cos_add_sin_mul_sin theta
    apply Prod.ext <;> dsimp
    · conv_rhs => rw [← one_smul ℝ x.1, ← htrig]
      module
    · conv_rhs => rw [← one_smul ℝ x.2, ← htrig]
      module
  map_add' x y := by
    apply Prod.ext <;> simp <;> module
  map_smul' r x := by
    apply Prod.ext <;> simp [smul_smul] <;> module

end TauCeti
end
