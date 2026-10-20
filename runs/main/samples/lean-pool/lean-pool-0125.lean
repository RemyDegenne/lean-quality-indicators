@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_450_3 :
    Uω (aρ 3) (bρ 3) (473184300463 / 1000000000000 : ℝ) ≤
      (-(971918216274480697521 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9190751438634959 / 20000000000000000 : ℝ) ≤
      (-(971918216274480697521 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (9190751438634959 / 20000000000000000 : ℝ) =
            (9190751438634959 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9190751438634959 / 5000000000000000 : ℝ) ≤
            (760949734475519302479 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4594570770949959 / 10000000000000000 : ℝ)) (q :=
      (9190751438634959 / 20000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

end Zeta5Irrational
end
