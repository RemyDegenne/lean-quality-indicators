@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_440_1 :
    Uω (aρ 1) (bρ 1) (1853008205557 / 4000000000000 : ℝ) ≤
      (-(979390335049681997199 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9135975808641307 / 20000000000000000 : ℝ) ≤
      (-(979390335049681997199 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (9135975808641307 / 20000000000000000 : ℝ) =
            (9135975808641307 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9135975808641307 / 5000000000000000 : ℝ) ≤
            (753477615700318002801 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4567952512833807 / 10000000000000000 : ℝ)) (q :=
      (9135975808641307 / 20000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

end Zeta5Irrational
end
