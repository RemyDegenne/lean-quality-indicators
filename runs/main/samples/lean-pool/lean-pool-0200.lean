@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_596_3 :
    Uω (aρ 3) (bρ 3) (44120943545411 / 64000000000000 : ℝ) ≤
      (-(1959521580007089325513 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54061501675977919 / 80000000000000000 : ℝ) ≤
      (-(1959521580007089325513 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (54061501675977919 / 80000000000000000 : ℝ) =
            (54061501675977919 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (54061501675977919 / 40000000000000000 : ℝ) ≤
            (1506214321492910674487 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6757140326969011 / 10000000000000000 : ℝ)) (q :=
      (54061501675977919 / 80000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

end Zeta5Irrational
end
