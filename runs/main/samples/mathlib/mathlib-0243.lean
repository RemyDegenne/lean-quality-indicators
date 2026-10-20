@[expose] public section

noncomputable section

open Function Set Filter

open scoped Topology Filter ContDiff

variable {E X : Type*}

namespace ContDiffBump

theorem one_lt_rOut_div_rIn {c : E} (f : ContDiffBump c) : 1 < f.rOut / f.rIn := by
  rw [one_lt_div f.rIn_pos]
  exact f.rIn_lt_rOut

end ContDiffBump
end
end
