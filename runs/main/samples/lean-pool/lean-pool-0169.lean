@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_93_4 :
    Uω (aρ 4) (bρ 4) (790260808521 / 16000000000000 : ℝ) ≤
      (-(18748829261004226629189 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (117616265462433 / 5000000000000000 : ℝ) ≤
      (-(18748829261004226629189 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (117616265462433 / 5000000000000000 : ℝ) =
            (117616265462433 / 78125000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (117616265462433 / 78125000000000 : ℝ) ≤
            (2045586147995773370811 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (190508574534107 / 10000000000000000 : ℝ)) (q :=
      (117616265462433 / 5000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

end Zeta5Irrational
end
