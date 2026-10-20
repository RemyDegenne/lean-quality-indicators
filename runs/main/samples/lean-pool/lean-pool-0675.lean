@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_467_5 :
    Uω (aρ 5) (bρ 5) (16577867570387 / 32000000000000 : ℝ) ≤
      (-(7250633714693489879047 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19371755092659821 / 40000000000000000 : ℝ) ≤
      (-(7250633714693489879047 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (19371755092659821 / 40000000000000000 : ℝ) =
            (19371755092659821 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19371755092659821 / 10000000000000000 : ℝ) ≤
            (6612309891306510120953 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4837440367928973 / 10000000000000000 : ℝ)) (q :=
      (19371755092659821 / 40000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

end Zeta5Irrational
end
