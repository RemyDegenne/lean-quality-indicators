@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_609_4 :
    Uω (aρ 4) (bρ 4) (22553704112181 / 32000000000000 : ℝ) ≤
      (-(119027858978336842039 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27330144991045187 / 40000000000000000 : ℝ) ≤
      (-(119027858978336842039 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (27330144991045187 / 40000000000000000 : ℝ) =
            (27330144991045187 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (27330144991045187 / 20000000000000000 : ℝ) ≤
            (97580634865413157961 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6830996478476031 / 10000000000000000 : ℝ)) (q :=
      (27330144991045187 / 40000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

end Zeta5Irrational
end
