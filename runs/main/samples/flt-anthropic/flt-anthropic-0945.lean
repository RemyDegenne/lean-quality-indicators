namespace P2MW.S_AutomorphicForm_satakeData_eq_of_under_eq_of_twistedCutTrace_ne_zero_of_heckeWordShift

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain AutomorphicForm MeasureTheory

open scoped Pointwise NumberField TensorProduct

noncomputable section

namespace R3Sigma

section Local

variable (L : Type) [Field L] [NumberField L]

variable {L}

theorem mem_Kw_iff (w : HeightOneSpectrum (𝓞 L)) (x : GL (Fin 2) (w.adicCompletion L)) :
    x ∈ Kw L w ↔ (∀ i j, (x : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L) ∧
      ∀ i j, ((x⁻¹ : GL (Fin 2) (w.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
        w.adicCompletionIntegers L := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Matrix.GeneralLinearGroup.map_apply]
      exact (y i j).2
    · rw [← map_inv, Matrix.GeneralLinearGroup.map_apply]
      exact ((y⁻¹ : GL (Fin 2) (w.adicCompletionIntegers L)) i j).2
  · rintro ⟨h1, h2⟩
    set O := w.adicCompletionIntegers L
    let M : Matrix (Fin 2) (Fin 2) O := Matrix.of fun i j => ⟨_, h1 i j⟩
    let M' : Matrix (Fin 2) (Fin 2) O := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hf : Function.Injective (algebraMap O (w.adicCompletion L)) := Subtype.val_injective
    have hM : M.map (algebraMap O (w.adicCompletion L)) = (x : Matrix _ _ _) := by
      ext i j; rfl
    have hM' : M'.map (algebraMap O (w.adicCompletion L)) = ((x⁻¹ : GL (Fin 2) _) : Matrix _ _ _) := by
      ext i j; rfl
    have hinj := Matrix.map_injective (m := Fin 2) (n := Fin 2) hf
    have hMM' : M * M' = 1 := by
      apply hinj
      show (M * M').map _ = (1 : Matrix (Fin 2) (Fin 2) O).map _
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, mul_inv_cancel,
        Units.val_one]
    have hM'M : M' * M = 1 := by
      apply hinj
      show (M' * M).map _ = (1 : Matrix (Fin 2) (Fin 2) O).map _
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
    refine ⟨⟨M, M', hMM', hM'M⟩, Units.ext ?_⟩
    exact hM

end Local
end R3Sigma
end
end P2MW.S_AutomorphicForm_satakeData_eq_of_under_eq_of_twistedCutTrace_ne_zero_of_heckeWordShift
