@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_655_13 :
    Uω (aρ 13) (bρ 13) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(8998545100638613692049 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (52048488400157723 / 128000000000000000 : ℝ) ≤
      (-(8998545100638613692049 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (52048488400157723 / 128000000000000000 : ℝ) =
            (52048488400157723 / 32000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (52048488400157723 / 32000000000000000 : ℝ) ≤
            (4864398505361386307951 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (176073881258241 / 500000000000000 : ℝ)) (q :=
      (52048488400157723 / 128000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

end Zeta5Irrational
end
