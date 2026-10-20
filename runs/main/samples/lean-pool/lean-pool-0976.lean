@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_142_3 :
    Uω (aρ 3) (bρ 3) (1423546864539 / 16000000000000 : ℝ) ≤
      (-(25914457472574753600061 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1498233167106849 / 20000000000000000 : ℝ) ≤
      (-(25914457472574753600061 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (1498233167106849 / 20000000000000000 : ℝ) =
            (1498233167106849 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1498233167106849 / 1250000000000000 : ℝ) ≤
            (1811429739425246399939 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (372089356857487 / 5000000000000000 : ℝ)) (q :=
      (1498233167106849 / 20000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

end Zeta5Irrational
end
