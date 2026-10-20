@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_650_3 :
    Uω (aρ 3) (bρ 3) (770823404286711 / 1024000000000000 : ℝ) ≤
      (-(1511333213172008917413 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (946100418468559111 / 1280000000000000000 : ℝ) ≤
      (-(1511333213172008917413 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (946100418468559111 / 1280000000000000000 : ℝ) =
            (946100418468559111 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (946100418468559111 / 640000000000000000 : ℝ) ≤
            (1954402688327991082587 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (923863633503603 / 1250000000000000 : ℝ)) (q :=
      (946100418468559111 / 1280000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

end Zeta5Irrational
end
