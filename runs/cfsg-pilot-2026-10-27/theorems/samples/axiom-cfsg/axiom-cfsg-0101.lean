@[expose] public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native Subgroup

theorem rep_aH :
    Rep 276 (genArr 0) (perm aH) := by rw [perm_aH]; exact rep_g0

end CFSG.EvenSmallLie.SympSix.Co3Ident
end
