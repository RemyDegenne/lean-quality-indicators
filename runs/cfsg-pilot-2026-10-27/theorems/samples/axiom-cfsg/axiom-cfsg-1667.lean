public section

namespace CFSG.StandardType

open CFSG.Timmesfeld

theorem coxeterMatrixE7_eq_three (i j : Fin 7) (h : edgeE 7 i j) :
    (CoxeterMatrix.E₇ : CoxeterMatrix (Fin 7)).M i j = 3 := by
  fin_cases i <;> fin_cases j <;> simp_all [edgeE, CoxeterMatrix.E₇] <;> rfl

end CFSG.StandardType
end
