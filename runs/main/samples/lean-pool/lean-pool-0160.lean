@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_234_7 :
    Uω (aρ 7) (bρ 7) (2820231956767 / 16000000000000 : ℝ) ≤
      (-(24139057684859532006813 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1789303618169693 / 20000000000000000 : ℝ) ≤
      (-(24139057684859532006813 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (1789303618169693 / 20000000000000000 : ℝ) =
            (1789303618169693 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1789303618169693 / 1250000000000000 : ℝ) ≤
            (3586829527140467993187 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (374853419217659 / 5000000000000000 : ℝ)) (q :=
      (1789303618169693 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

end Zeta5Irrational
end
