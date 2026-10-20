@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_362_9 :
    Uω (aρ 9) (bρ 9) (2338577156961 / 6400000000000 : ℝ) ≤
      (-(3913833307851789537159 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1671812250119869 / 8000000000000000 : ℝ) ≤
      (-(3913833307851789537159 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (1671812250119869 / 8000000000000000 : ℝ) =
            (1671812250119869 / 1000000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1671812250119869 / 1000000000000000 : ℝ) ≤
            (1284770544398210462841 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (187305929049311 / 1000000000000000 : ℝ)) (q :=
      (1671812250119869 / 8000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

end Zeta5Irrational
end
