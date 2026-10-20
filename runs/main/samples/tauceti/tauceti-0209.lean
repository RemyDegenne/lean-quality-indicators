public section

open Matrix

open scoped MatrixGroups

namespace TauCeti

open scoped RightActions

@[simp]
theorem TraceFormulaMatrixModule.op_smul_mk (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    TraceFormulaMatrixModule.mk A <• (g : PSL(2, ℤ)) =
      TraceFormulaMatrixModule.mk (traceFormulaMatrixRight g⁻¹ A) := by
  rw [op_smul_eq_rightPSL_inv, ← QuotientGroup.mk_inv, rightPSL_coe, right_mk]

end TauCeti
end
