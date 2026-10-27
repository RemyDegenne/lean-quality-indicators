public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Ord

open Matrix

open scoped MatrixGroups

variable {F : Type} [Field F]

theorem trace_conj_SL (G M : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((G * M * G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace =
      (M : Matrix (Fin 2) (Fin 2) F).trace := by
  have h1 : ((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (G : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Ord
end
