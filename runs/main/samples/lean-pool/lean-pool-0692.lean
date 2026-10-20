@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_231_7 :
    Uω (aρ 7) (bρ 7) (10997027650713 / 64000000000000 : ℝ) ≤
      (-(12378411562319641158947 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1345689348787241 / 16000000000000000 : ℝ) ≤
      (-(12378411562319641158947 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (1345689348787241 / 16000000000000000 : ℝ) =
            (1345689348787241 / 1000000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1345689348787241 / 1000000000000000 : ℝ) ≤
            (1484532043680358841053 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (137374861761029 / 2000000000000000 : ℝ)) (q :=
      (1345689348787241 / 16000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

end Zeta5Irrational
end
