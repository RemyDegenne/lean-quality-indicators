@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_638_4 :
    Uω (aρ 4) (bρ 4) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(20751000980978739367 / 62500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14349516634027087 / 20000000000000000 : ℝ) ≤
      (-(20751000980978739367 / 62500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14349516634027087 / 20000000000000000 : ℝ) =
            (14349516634027087 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14349516634027087 / 10000000000000000 : ℝ) ≤
            (22570697787771260633 / 62500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7173291991739587 / 10000000000000000 : ℝ)) (q :=
      (14349516634027087 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

end Zeta5Irrational
end
