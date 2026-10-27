public section

namespace CFSG.GH74.Generic.S1.Exo

open Module Matrix CFSG.RankThree.PartOne.KCOrthogonal

open scoped MatrixGroups

section Act

variable {K E : Type} [Field K] [Finite K] [Field E] [Algebra K E] (D : OddNormPlane K E)

theorem hermOddCongr_mem (g : Matrix (Fin 2) (Fin 2) E) {X : Matrix (Fin 2) (Fin 2) E}
    (hX : X ∈ hermOddSpace D.σ) : hermOddCongr D.σ g X ∈ hermOddSpace D.σ := by
  intro i j
  have e00 := hX 0 0
  have e01 := hX 0 1
  have e10 := hX 1 0
  have e11 := hX 1 1
  simp only [hermOddCongr_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Fin.sum_univ_two, map_add, map_mul, D.sigma_sigma, e00, e01, e10, e11]
  fin_cases i <;> fin_cases j <;> simp <;> ring

end Act
end CFSG.GH74.Generic.S1.Exo
end
