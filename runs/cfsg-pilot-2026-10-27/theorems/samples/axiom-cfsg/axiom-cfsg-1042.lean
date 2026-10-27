public section

namespace CFSG.SectionRank.OddCover

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank

open scoped commutatorElement

variable {K : Type*} [Field K]

theorem slD_mul_slU (a : Kˣ) (t : K) : slD a * slU t = slU ((a : K) ^ 2 * t) * slD a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_slU, coe_slD, Matrix.mul_apply, Fin.sum_univ_two, sq, mul_assoc]
  field_simp

end CFSG.SectionRank.OddCover
end
