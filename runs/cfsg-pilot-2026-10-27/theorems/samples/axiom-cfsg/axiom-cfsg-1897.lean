public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.Sec4

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

open CFSG.Assembly.LowTwoRank (StatedScalars)

open Matrix

open scoped commutatorElement

namespace Res5Proof

section Matrices

variable {K : Type} [Field K]

theorem swapTwelve_comm_diagE (e : Kˣ) : swapTwelve K * diagE e = diagE e * swapTwelve K := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_swapTwelve, coe_diagE]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, diagonal]

end Matrices
end Res5Proof
end CFSG.RankThree.PartTwo.Sec13
end
