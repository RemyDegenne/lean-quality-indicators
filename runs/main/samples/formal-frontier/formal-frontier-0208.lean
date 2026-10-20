set_option autoImplicit false

set_option relaxedAutoImplicit false

set_option linter.mathlibStandardSet true

set_option linter.style.header false

@[expose] public noncomputable section

open scoped BigOperators

open TensorProduct

universe u v v' w w'

namespace Coalgebra

section CoefficientMatrixReindex

variable {R : Type u} {A : Type v} {ι : Type w} {κ : Type w'}
  [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]

theorem coefficientMatrix_comul_reindex [Fintype ι] [Fintype κ]
    (M : Matrix ι ι A)
    (hΔ : ∀ i j, comul (R := R) (M i j) = ∑ k, M i k ⊗ₜ[R] M k j)
    (e : ι ≃ κ) :
    ∀ i j, comul (R := R) (Matrix.reindex e e M i j) =
      ∑ k, Matrix.reindex e e M i k ⊗ₜ[R] Matrix.reindex e e M k j := by
  intro i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hΔ (e.symm i) (e.symm j)]
  exact (e.symm.sum_comp fun k => M (e.symm i) k ⊗ₜ[R] M k (e.symm j)).symm

end CoefficientMatrixReindex
end Coalgebra
end
