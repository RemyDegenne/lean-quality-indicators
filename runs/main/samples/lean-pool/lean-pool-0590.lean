@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_254_3 :
    Uω (aρ 3) (bρ 3) (3456533023273 / 16000000000000 : ℝ) ≤
      (-(1997601945127060592757 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (404568433500703 / 2000000000000000 : ℝ) ≤
      (-(1997601945127060592757 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (404568433500703 / 2000000000000000 : ℝ) =
            (404568433500703 / 250000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (404568433500703 / 250000000000000 : ℝ) ≤
            (601699980997939407243 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (404202706481281 / 2000000000000000 : ℝ)) (q :=
      (404568433500703 / 2000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

end Zeta5Irrational
end
