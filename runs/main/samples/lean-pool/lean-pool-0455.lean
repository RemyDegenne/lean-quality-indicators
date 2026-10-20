@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_5_2 :
    Uω (aρ 2) (bρ 2) (78667711 / 1000000000000 : ℝ) ≤
      (-(24603999536613700227217 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (145865890759319 / 20000000000000000 : ℝ) ≤
      (-(24603999536613700227217 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (145865890759319 / 20000000000000000 : ℝ) =
            (145865890759319 / 78125000000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (145865890759319 / 78125000000000 : ℝ) ≤
            (3121887675386299772783 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (58386337274319 / 10000000000000000 : ℝ)) (q :=
      (145865890759319 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

end Zeta5Irrational
end
