public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.Blueprint CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.HardMathSupport.Solomon.Coordinator.SuzPump CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Sporadic.SuzOddCore (suzM suzT suzEquivM suzM_le_suzT)

namespace SuzCopy

section Classes

theorem exists_rep_of_mem_C {i : Fin 6} {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzFiveC i) :
    ∃ k < (suzFiveCCert i).pts.size, Rep 1782 (suzFiveCCert i).pts[k]! s :=
  enumOK_exists_rep suzFiveKeys_lt (suzFiveC_check_spec i.2).1 hs

end Classes
end SuzCopy
end CFSG.HardMathSupport.Solomon.Coordinator.YS08
end
