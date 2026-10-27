public section

namespace CFSG.Quasithin.A312U3

open Matrix

open scoped MatrixGroups

section TwoByTwo

variable {F : Type*} [Field F]

theorem fin_two_mul_self' (M : Matrix (Fin 2) (Fin 2) F) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

end TwoByTwo
end CFSG.Quasithin.A312U3
end
