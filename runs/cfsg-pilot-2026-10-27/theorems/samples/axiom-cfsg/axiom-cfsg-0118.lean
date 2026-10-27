public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false

section SigFixed

open T7

variable {L : Type} [Field L] [CharP L 2] {Fr : L →+* L}

theorem sig_thn {c : L} (hc : Fr c = c) :
    sigHom Fr (pinnedX Tag.F4 L (-highRoot Tag.F4) c) = pinnedX Tag.F4 L (-highRoot Tag.F4) c :=
  sig_root_fixed (IsRoot.neg isRoot_theta) (by rw [smul_neg, w_smul_theta]) hc

end SigFixed
end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even
end
