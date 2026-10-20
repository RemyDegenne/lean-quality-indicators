@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_394_2 :
    Uω (aρ 2) (bρ 2) (24976397424531 / 64000000000000 : ℝ) ≤
      (-(4819509720196513865331 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1220485664574031 / 3200000000000000 : ℝ) ≤
      (-(4819509720196513865331 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (1220485664574031 / 3200000000000000 : ℝ) =
            (1220485664574031 / 800000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1220485664574031 / 800000000000000 : ℝ) ≤
            (2111962082803486134669 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (152549581463989 / 400000000000000 : ℝ)) (q :=
      (1220485664574031 / 3200000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

end Zeta5Irrational
end
