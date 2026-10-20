@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_222_7 :
    Uω (aρ 7) (bρ 7) (2108557473709 / 12800000000000 : ℝ) ≤
      (-(12939557978942782377787 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6014150070893521 / 80000000000000000 : ℝ) ≤
      (-(12939557978942782377787 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (6014150070893521 / 80000000000000000 : ℝ) =
            (6014150070893521 / 5000000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6014150070893521 / 5000000000000000 : ℝ) ≤
            (923385627057217622213 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (72409398079153 / 1250000000000000 : ℝ)) (q :=
      (6014150070893521 / 80000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

end Zeta5Irrational
end
