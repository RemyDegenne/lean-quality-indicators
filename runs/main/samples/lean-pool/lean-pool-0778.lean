@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_508_10 :
    Uω (aρ 10) (bρ 10) (17856057682947 / 32000000000000 : ℝ) ≤
      (-(10114145609446987792001 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14548165346591567 / 40000000000000000 : ℝ) ≤
      (-(10114145609446987792001 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (14548165346591567 / 40000000000000000 : ℝ) =
            (14548165346591567 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14548165346591567 / 10000000000000000 : ℝ) ≤
            (3748797996553012207999 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1715089576907423 / 5000000000000000 : ℝ)) (q :=
      (14548165346591567 / 40000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

end Zeta5Irrational
end
