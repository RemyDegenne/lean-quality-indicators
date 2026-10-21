namespace OAI

section

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators

open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem QuaternionLift.matrixAction_conjugate {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (s : Fin 3) (M : Mat) :
    matrixAction s (conjugateMatrix R M) =
      conjugateMatrix R (∑ r, R r s • matrixAction r M) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  rw [matrixAction_eq_commutator, ← P.conjugate_rotation hR s,
    conjugateMatrix_mul R hR', conjugateMatrix_mul R hR', ← conjugateMatrix_sub]
  congr 1
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    matrixAction_eq_commutator, smul_sub, Finset.sum_sub_distrib]

end
end PositiveEinsteinFour.QuaternionFrame
end
end OAI
