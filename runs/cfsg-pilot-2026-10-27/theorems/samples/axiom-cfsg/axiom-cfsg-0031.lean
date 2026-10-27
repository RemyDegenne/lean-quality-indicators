public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem mem_fixedSub {S : Type*} [Group S] {α : MulAut S} {s : S} : s ∈ fixedSub α ↔ α s = s :=
  Iff.rfl

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
end
