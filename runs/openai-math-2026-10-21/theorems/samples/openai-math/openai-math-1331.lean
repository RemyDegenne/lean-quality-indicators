namespace OAI

namespace ThorpNine.Tail

namespace Thorp

open scoped BigOperators

open Filter

lemma log_three_quarters_lower : -(1 : ℝ) ≤ Real.log (3 / 4 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
  have he : Real.log (4 / 3 : ℝ) = - Real.log (3 / 4 : ℝ) := by
    rw [← Real.log_inv]
    congr 1
    norm_num
  rw [he] at h
  linarith

end Thorp
end ThorpNine.Tail
end OAI
