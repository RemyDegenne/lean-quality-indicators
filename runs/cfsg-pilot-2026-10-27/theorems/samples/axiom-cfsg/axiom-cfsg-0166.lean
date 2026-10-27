public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup

open scoped commutatorElement

theorem exists_SL2_mul_col_eq {F : Type*} [Field F] {X : Matrix (Fin 2) (Fin 1) F}
    (hX : X ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      A.val * (!![1; 0] : Matrix (Fin 2) (Fin 1) F) = X := by
  by_cases h0 : X 0 0 = 0
  · have h1 : X 1 0 ≠ 0 := fun h1 => hX (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h0, h1])
    refine ⟨⟨!![0, -(X 1 0)⁻¹; X 1 0, 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two_of, h1]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![X 0 0, 0; X 1 0, (X 0 0)⁻¹], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two_of, h0]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end CFSG.Quasithin.H13.NQCat
end
