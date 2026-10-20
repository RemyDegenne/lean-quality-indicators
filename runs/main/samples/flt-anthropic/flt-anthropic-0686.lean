namespace P2MW.S_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open AutomorphicForm AutomorphicForm.WindowedSiegel Matrix

open scoped ComplexConjugate

namespace R4ArchPolyR

section Rot

scoped instance fact_two_pi_pos : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨two_pi_pos⟩

theorem rotO_add (θ₁ θ₂ : ℝ) : rotO (θ₁ + θ₂) = rotO θ₁ * rotO θ₂ := by
  apply Subtype.ext
  change rotMat (θ₁ + θ₂) = rotMat θ₁ * rotMat θ₂
  ext i j
  fin_cases i <;> fin_cases j <;>
    { simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add]
      try ring }

end Rot
end R4ArchPolyR
end
end P2MW.S_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal
