public section

namespace CFSG.Quasithin.H13.KG4413

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

open scoped MatrixGroups

section Cycle

variable {F : Type} [Field F]

variable [CharP F 2]

theorem wJ_mul_cyc3iSL_mul_wJ : (wJ : SL(3, F)) * cyc3iSL F * wJ = cyc3SL F := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, cyc3SL_coe,
    cyc3iSL_coe, wJ_coe]
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [cyc3Mat, cyc3iMat, wJMat]

end Cycle
end CFSG.Quasithin.H13.KG4413
end
