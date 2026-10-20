@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_293_8 :
    Uω (aρ 8) (bρ 8) (41730554821 / 160000000000 : ℝ) ≤
      (-(19487658528202780408503 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1424497670143987 / 10000000000000000 : ℝ) ≤
      (-(19487658528202780408503 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (1424497670143987 / 10000000000000000 : ℝ) =
            (1424497670143987 / 1250000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1424497670143987 / 1250000000000000 : ℝ) ≤
            (1306756880797219591497 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (623712754280237 / 5000000000000000 : ℝ)) (q :=
      (1424497670143987 / 10000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

end Zeta5Irrational
end
