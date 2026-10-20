@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_667_13 :
    Uω (aρ 13) (bρ 13) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(802010272264151745109 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14349651124315259 / 32000000000000000 : ℝ) ≤
      (-(802010272264151745109 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (14349651124315259 / 32000000000000000 : ℝ) =
            (14349651124315259 / 8000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14349651124315259 / 8000000000000000 : ℝ) ≤
            (584284088335848254891 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (199511858027637 / 500000000000000 : ℝ)) (q :=
      (14349651124315259 / 32000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

end Zeta5Irrational
end
