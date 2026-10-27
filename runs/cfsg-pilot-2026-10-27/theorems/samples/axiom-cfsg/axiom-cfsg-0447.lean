public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Fl3

open Subgroup Matrix CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open scoped MatrixGroups

variable {F : Type} [Field F]

theorem gAut_coe (A : GL (Fin 3) F) (σ : F ≃+* F) (x : SL(3, F)) :
    ((gAut A σ x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) *
        σ.toRingHom.mapMatrix ((((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ) *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [gAut, MulAut.mul_apply, MulAut.mul_apply,
    CatalogueBHigherLinearAction.slConjugation_matrix]
  have h1 : ((CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ
      (CatalogueBGraphForm.slGraphAut 3 F x) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      σ.toRingHom.mapMatrix ((((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ) := by
    ext i j
    rfl
  rw [h1]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Fl3
end
