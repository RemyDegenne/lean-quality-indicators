public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open Matrix CFSG.RankThree.PartOne.CTP

open CFSG.HardMathSupport.Seitz.TrialityOdd.Proving (sl2Range u2_mem_sl2Range l2_mem_sl2Range)

open CFSG.HardMathSupport.Foote.ModuleExclusions (Ai hilbert90_matrix)

section Basic

variable {K : Type} [Field K]

theorem eq_scalar_of_conj_eq_scalar {g : GL (Fin 2) K} {M : Matrix (Fin 2) (Fin 2) K} {s : K}
    (h : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M * (g : Matrix (Fin 2) (Fin 2) K) =
      s • (1 : Matrix (Fin 2) (Fin 2) K)) :
    M = Matrix.scalar (Fin 2) s := by
  calc M = (g : Matrix (Fin 2) (Fin 2) K) *
        (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M * (g : Matrix (Fin 2) (Fin 2) K)) *
        ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
        simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one]
    _ = Matrix.scalar (Fin 2) s := by
        rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv,
          Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

end Basic
end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
end
