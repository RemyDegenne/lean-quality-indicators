namespace P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled

set_option autoImplicit false

open MeasureTheory NumberField

open scoped TensorProduct

open scoped TensorProduct.RightActions

noncomputable section

namespace R1SigmaConjScalar

section LinearAlgebra

variable {R : Type*} [CommRing R]

theorem exists_eq_scalar_of_commute_unip (ε : GL (Fin 2) R)
    (h₁ : (unipUpper : GL (Fin 2) R) * ε = ε * unipUpper)
    (h₂ : (unipLower : GL (Fin 2) R) * ε = ε * unipLower) :
    ∃ d : Rˣ, ε = Matrix.GeneralLinearGroup.scalar (Fin 2) d := by
  have h₁' : !![(1 : R), 1; 0, 1] * (ε : Matrix (Fin 2) (Fin 2) R) = ε * !![(1 : R), 1; 0, 1] := by
    simpa using congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) h₁
  have h₂' : !![(1 : R), 0; 1, 1] * (ε : Matrix (Fin 2) (Fin 2) R) = ε * !![(1 : R), 0; 1, 1] := by
    simpa using congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) h₂
  obtain ⟨hc, hb, hd⟩ := entries_of_commute_unip (ε : Matrix (Fin 2) (Fin 2) R) h₁' h₂'

  have hinv : (ε : Matrix (Fin 2) (Fin 2) R) 0 0 * (ε⁻¹ : GL (Fin 2) R) 0 0 = 1 := by
    have h := congrFun (congrFun (ε.mul_inv) 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
    rw [hb, zero_mul, add_zero] at h
    exact h
  refine ⟨⟨(ε : Matrix (Fin 2) (Fin 2) R) 0 0, (ε⁻¹ : GL (Fin 2) R) 0 0, hinv, by rw [mul_comm]; exact hinv⟩, ?_⟩
  ext i j
  change (ε : Matrix (Fin 2) (Fin 2) R) i j = Matrix.scalar (Fin 2) ((ε : Matrix (Fin 2) (Fin 2) R) 0 0) i j
  fin_cases i <;> fin_cases j
  · simp
  · simpa using hb
  · simpa using hc
  · simpa using hd

end LinearAlgebra
end R1SigmaConjScalar
end
end P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled
