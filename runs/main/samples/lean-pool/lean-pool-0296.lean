@[expose] public section

open scoped ComplexConjugate BigOperators

open Complex

theorem norm_of_sq_add_sq_eq_norm_sq_add_norm_sq_iff (α₁ α₂ : ℂ) :
    norm (α₁ ^ 2 + α₂ ^ 2) = norm α₁ ^ 2 + norm α₂ ^ 2 ↔
      α₁.re * α₂.im = α₂.re * α₁.im := by
  let α := ![α₁, α₂]
  have h₀ : α 0 = α₁ := rfl
  have h₁ : α 1 = α₂ := rfl
  have hy :
    norm (∑ i : Fin 2, α i ^ 2) = norm (α 0 ^ 2 + α 1 ^ 2) ∧
      ∑ i : Fin 2, norm (α i) ^ 2 = norm (α 0) ^ 2 + norm (α 1) ^ 2 := by
    simp [Fin.sum_univ_two]
  simp_rw [← h₀, ← h₁, ← hy.1, ← hy.2, norm_of_sum_sq_eq_sum_norm_sq_iff,
    Fin.forall_fin_two, h₀, h₁, true_and, and_true, eq_comm, and_self_iff]

end
