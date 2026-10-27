public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

set_option linter.unusedSectionVars false

section Fin

variable {L : Type} [Field L]

theorem vA7_data : vA7 ∈ rootFinset Tag.E8 ∧ vA7 7 = 0 := by
  unfold vA7
  simp only [rootFinset_E8_eq]
  decide +kernel

end Fin
end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
end
