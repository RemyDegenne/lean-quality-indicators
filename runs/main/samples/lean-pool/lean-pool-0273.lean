@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_437_6 :
    Uω (aρ 6) (bρ 6) (922531203149 / 2000000000000 : ℝ) ≤
      (-(4460068031353997442141 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2049148427531953 / 5000000000000000 : ℝ) ≤
      (-(4460068031353997442141 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (2049148427531953 / 5000000000000000 : ℝ) =
            (2049148427531953 / 1250000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2049148427531953 / 1250000000000000 : ℝ) ≤
            (2471403771646002557859 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1020831126716953 / 2500000000000000 : ℝ)) (q :=
      (2049148427531953 / 5000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

end Zeta5Irrational
end
