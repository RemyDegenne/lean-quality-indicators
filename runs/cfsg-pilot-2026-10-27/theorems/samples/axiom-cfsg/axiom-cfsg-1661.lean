public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false

section Generic

theorem twNormalizer (c : TwClass) (K : Type) [Field K] [Finite K] (hK : c.minQ ≤ Nat.card K)
    (D : LangLevi c.tag K c.w) : TwFrameNormalizerSolvable c.tag K (c.X₁ D ⊔ c.X₂ D) := by
  cases c
  · exact twNormalizer_f4Six K hK D
  · exact twNormalizer_e6Six K hK D
  · exact twNormalizer_e8Ten K hK D
  · exact twNormalizer_e8Twelve K hK D

end Generic
end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
end
