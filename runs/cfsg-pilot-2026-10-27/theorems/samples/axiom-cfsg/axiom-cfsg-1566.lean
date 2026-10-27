public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

set_option linter.unusedSectionVars false

section Transport

variable {K : Type} [Field K] [Finite K] {w : WeylGroup Tag.E8} (D : LangLevi Tag.E8 K w)

theorem iotaV_injective : Function.Injective (iotaV D) := by
  intro v v' h
  funext ν
  exact (algebraMap K D.L).injective (congrFun h ν)

end Transport
end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8
end
