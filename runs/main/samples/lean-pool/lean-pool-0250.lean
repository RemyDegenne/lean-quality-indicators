@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_631_4 :
    Uω (aρ 4) (bρ 4) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(3413533862948097198867 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28432306957705233 / 40000000000000000 : ℝ) ≤
      (-(3413533862948097198867 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28432306957705233 / 40000000000000000 : ℝ) =
            (28432306957705233 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28432306957705233 / 20000000000000000 : ℝ) ≤
            (3517937940051902801133 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3553298329204277 / 5000000000000000 : ℝ)) (q :=
      (28432306957705233 / 40000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

end Zeta5Irrational
end
