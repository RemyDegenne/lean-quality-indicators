public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false

section Weak

variable {K K' : Type*} [Group K] [Group K'] {p k : ℕ}

theorem i1910_weakAbs_of_abs (h : IsLocallyBalancedAbs p k K) :
    IsWeaklyLocallyBalancedAbs p k K :=
  fun A _ => i1910_weak_of_strong (h.isLocallyBalanced A)

end Weak
end CFSG.HardMathSupport.Solomon.Coordinator
end
