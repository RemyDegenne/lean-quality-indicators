@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_213_4 :
    Uω (aρ 4) (bρ 4) (20574554419651 / 128000000000000 : ℝ) ≤
      (-(988139645586834072963 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (886937020876051 / 6400000000000000 : ℝ) ≤
      (-(988139645586834072963 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (886937020876051 / 6400000000000000 : ℝ) =
            (886937020876051 / 800000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (886937020876051 / 800000000000000 : ℝ) ≤
            (51581124863165927037 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (55129905768497 / 400000000000000 : ℝ)) (q :=
      (886937020876051 / 6400000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

end Zeta5Irrational
end
