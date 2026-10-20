@[expose] public section

open scoped QInterval

namespace ComputableℝSeq

section Pi

theorem sqrtTwoAddSeriesN_lb_le (n k : ℕ) : (sqrtTwoAddSeriesN n).lb k ≤ Real.sqrtTwoAddSeries 0
  n := by
  rw [← IsComputable.prop (x := Real.sqrtTwoAddSeries 0 n)]
  exact ComputableℝSeq.hlb _ _

end Pi
end ComputableℝSeq
end
