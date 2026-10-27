public section

section FusTor

open CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusTor

theorem bar_mul_eq_one_fus {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {a : Kˣ} (ha : a ^ (p ^ f + 1) = 1) : h.bar (a : K) * (a : K) = 1 := by
  rw [h.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, ha, Units.val_one]

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusTor
end FusTor
end
