public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.Models

open scoped MatrixGroups

namespace ChainL

variable {F : Type} [Field F]

theorem inv_matrix_block (A : GL (Fin 3) F) (u w : F) (hu : u ≠ 0) (hw : w ≠ 0)
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = !![0, u, 0; -u, 0, 0; 0, 0, w]) :
    ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, -u⁻¹, 0; u⁻¹, 0, 0; 0, 0, w⁻¹] := by
  have h2 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h0 : (!![0, u, 0; -u, 0, 0; 0, 0, w] : Matrix (Fin 3) (Fin 3) F) *
      !![0, -u⁻¹, 0; u⁻¹, 0, 0; 0, 0, w⁻¹] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hu, hw]
  calc ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      = ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) *
        !![0, -u⁻¹, 0; u⁻¹, 0, 0; 0, 0, w⁻¹] := by
        rw [hA, Matrix.mul_assoc, h0, Matrix.mul_one]
    _ = !![0, -u⁻¹, 0; u⁻¹, 0, 0; 0, 0, w⁻¹] := by rw [h2, Matrix.one_mul]

end ChainL
end CFSG.ClassicalInvolution.ModelFacts.Orth15
end
