@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_497_11 :
    Uω (aρ 11) (bρ 11) (69906379973123 / 128000000000000 : ℝ) ≤
      (-(3087635739603101573631 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46531035444361763 / 160000000000000000 : ℝ) ≤
      (-(3087635739603101573631 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (46531035444361763 / 160000000000000000 : ℝ) =
            (46531035444361763 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (46531035444361763 / 40000000000000000 : ℝ) ≤
            (378100161896898426369 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1254767313894993 / 5000000000000000 : ℝ)) (q :=
      (46531035444361763 / 160000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

end Zeta5Irrational
end
