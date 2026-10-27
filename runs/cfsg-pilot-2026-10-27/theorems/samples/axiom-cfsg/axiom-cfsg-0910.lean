public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.M24Std.CU43

section Vacuous

theorem caseI5_vacuous {T y c k : Equiv.Perm (Fin 820)}
    (hT : Rep 820 (tabOf reps[5]!) T) (_hT2 : T * T = 1) (hs : SigRel T y c k) (hy : y ∈ R)
    (hc : c ∈ R) (hk : k ∈ R) : False := by
  rw [eq_of_rep hT (rep_tabOf_rP (by norm_num))] at hs
  exact Certificates.certificate27275 hs hy hc hk

end Vacuous
end CFSG.EvenSporadicStandard.HSStd.U43
end
