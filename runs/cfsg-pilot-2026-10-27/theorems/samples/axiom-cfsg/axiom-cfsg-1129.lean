public section

namespace CFSG.OddStandard.SmallF3.L33.KD

open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open CFSG.ComponentClassification.HSFLit.Sec8

namespace MB

open CFSG.ComponentClassification.HSFLit.Sec8.MB

theorem liftList_norms : ∀ D ∈ liftList, ∀ q ∈ D.norms, q.2.2.1 < 8 ∧
    compMB (sigOf D q.1) (conjMB q.2.2.2) = (r2Classes.getD q.2.2.1 ([], 1)).1 ∧
    applyMB (sigOf D q.1) q.2.2.2 * (D.s0 * q.2.1) * q.2.2.2 =
      (r2Classes.getD q.2.2.1 ([], 1)).2 := by decide +kernel

end MB
end Sec8
end CFSG.OddStandard.SmallF3.L33.KD
end
