public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix

open scoped Pointwise

@[simp] theorem extMat_last_castSucc (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) (j : Fin 5) :
    extMat A (Fin.last 5) j.castSucc = 0 := by
  simp only [extMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last,
    castSucc_ne_last5, if_false]

end
end CFSG.Quasithin.SimsF5
end
