public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.RankThree.PartOne.CTP

open scoped commutatorElement

namespace RootPair

section Trace

variable {F : Type} [Field F]

theorem trace_u2 (a : F) :
    Matrix.trace ((u2 a : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 2 := by
  rw [u2_coe, Matrix.trace_fin_two]
  simp [one_add_one_eq_two]

end Trace
end RootPair
end CFSG.LieType.SeitzGeneration
end
