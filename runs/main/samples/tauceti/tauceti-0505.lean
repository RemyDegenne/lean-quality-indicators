public section

noncomputable section

open MeasureTheory Module

open scoped RealInnerProductSpace

namespace selfAdjoint

theorem isHermitian_coe {p : ℕ} (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (A : Matrix (Fin p) (Fin p) ℝ).IsHermitian :=
  A.2

end selfAdjoint
end
end
