@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_585_11 :
    Uω (aρ 11) (bρ 11) (10887458103873 / 16000000000000 : ℝ) ≤
      (-(257572254535980578843 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4385720304765587 / 10000000000000000 : ℝ) ≤
      (-(257572254535980578843 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (4385720304765587 / 10000000000000000 : ℝ) =
            (4385720304765587 / 2500000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4385720304765587 / 2500000000000000 : ℝ) ≤
            (175644733151519421157 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4121370427255549 / 10000000000000000 : ℝ)) (q :=
      (4385720304765587 / 10000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

end Zeta5Irrational
end
