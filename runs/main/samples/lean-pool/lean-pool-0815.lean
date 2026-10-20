@[expose] public section

namespace TauCeti

open scoped InnerProductSpace BigOperators

open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [FiniteDimensional 𝕜 G]

namespace UnitarilyInvariantSeminorm

variable (N : UnitarilyInvariantSeminorm 𝕜 E F)

attribute [local instance] realModuleLinearMap

theorem kyFanSum_orthogonalBlockSum_self
    {E₀ F₀ : Type*}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 E₀] [FiniteDimensional 𝕜 F₀]
    (A : E₀ →ₗ[𝕜] F₀) (k : ℕ) :
    kyFanSum (2 * k) (orthogonalBlockSum A A) =
      2 * kyFanSum k A := by
  classical
  let e : Fin k × Fin 2 ≃ Fin (2 * k) :=
    finProdFinEquiv.trans (finCongr (by omega))
  unfold kyFanSum
  calc
    ∑ j : Fin (2 * k), (orthogonalBlockSum A A).singularValues (j : ℕ) =
        ∑ p : Fin k × Fin 2,
          (orthogonalBlockSum A A).singularValues (e p : ℕ) := by
      exact (e.sum_comp fun j => (orthogonalBlockSum A A).singularValues (j : ℕ)).symm
    _ = ∑ p : Fin k × Fin 2, A.singularValues (p.1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [singularValues_orthogonalBlockSum_self]
      congr 1
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change (p.2.val + 2 * p.1.val) / 2 = p.1.val
      omega
    _ = ∑ i : Fin k, ∑ _r : Fin 2, A.singularValues (i : ℕ) := by
      rw [Fintype.sum_prod_type]
    _ = 2 * ∑ i : Fin k, A.singularValues (i : ℕ) := by
      simp only [Fin.sum_univ_two]
      rw [Finset.sum_add_distrib]
      ring

end UnitarilyInvariantSeminorm
end TauCeti
end
