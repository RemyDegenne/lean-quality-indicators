public noncomputable section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Classical
  CFSG.Open CFSG.Timmesfeld.ExceptionalOrders

open scoped MatrixGroups

section Conj

variable {K : Type} [Field K]

theorem conjSL_diagUnitOne_HSL (l : Kˣ) : conjSL (diagUnitOne l) (HSL l : SL2 K) = HSL l := by
  ext i j
  rw [coe_conjSL, coe_diagUnitOne, coe_diagUnitOne_inv]
  fin_cases i <;> fin_cases j <;> simp [coe_HSL, Matrix.mul_apply, Fin.sum_univ_two]

end Conj
end CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
end
