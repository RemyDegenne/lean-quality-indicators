public section

namespace CFSG.Quasithin.F134.LieL3

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.Quasithin.SteinbergBS

open scoped LinearAlgebra.Projectivization MatrixGroups

variable {K : Type} [Field K]

theorem gammaZero_proj_inv [CharP K 2] (g : SL(3, K)) :
    ∃ h : SL(3, K), gammaZero K (proj 3 K g⁻¹) = proj 3 K h ∧
      (h : Matrix (Fin 3) (Fin 3) K) 1 0 = (g : Matrix (Fin 3) (Fin 3) K) 2 1 ∧
      (h : Matrix (Fin 3) (Fin 3) K) 2 0 = (g : Matrix (Fin 3) (Fin 3) K) 2 0 := by
  refine ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K
    (SpecialLinearGroup.toGL wJ) (g⁻¹⁻¹).transpose, ?_, ?_⟩
  · rw [gammaZero, MulAut.mul_apply, dualAut_proj, conjAut_proj]
  · have h2 : (((SpecialLinearGroup.toGL (wJ : SL(3, K)))⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = wJMat := by
      rw [← map_inv, wJ_inv]
      rfl
    have h1 : ((SpecialLinearGroup.toGL (wJ : SL(3, K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = wJMat := rfl
    rw [coe_slConjugation, h1, h2, inv_inv]
    constructor <;>
    simp [wJMat, Matrix.mul_apply, Fin.sum_univ_three, SpecialLinearGroup.coe_transpose,
      Matrix.vecMul, dotProduct]

end CFSG.Quasithin.F134.LieL3
end
