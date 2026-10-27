public section

namespace CFSG.GH74.Generic.BProg.B3.S45EvenN5D8

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryModel CFSG.GH74.Generic.BProg.B3.S45EvenN4Eig

variable {p f : ℕ} {K : Type} [Field K]

theorem br_unitary (h : UnitaryFieldData p f K) :
    ((br : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * br = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [br, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply]

end CFSG.GH74.Generic.BProg.B3.S45EvenN5D8
end
