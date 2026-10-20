public section

noncomputable section

open MeasureTheory Module

open scoped RealInnerProductSpace

namespace TauCeti

section symmetricEntry

variable {p : ℕ}

theorem trace_symmetricEntry_mul (i j : Fin p) {A : Matrix (Fin p) (Fin p) ℝ}
    (hA : A.IsHermitian) :
    (((symmetricEntry i j : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) * A).trace = A i j := by
  rw [coe_symmetricEntry, Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add,
    Matrix.trace_single_mul, Matrix.trace_single_mul]
  simp only [smul_eq_mul]
  have hsym : A j i = A i j := by simpa using hA.apply i j
  rw [hsym]
  ring

end symmetricEntry
end TauCeti
end
end
