@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_679_6 :
    Uω (aρ 6) (bρ 6) (4239911887007 / 4000000000000 : ℝ) ≤
      (23468035726243644037 / 2500000000000000000000 : ℝ) := by
  have hlg :
    Real.log (20188628247545629 / 20000000000000000 : ℝ) ≤
      (23468035726243644037 / 2500000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (10088235342513129 / 10000000000000000 : ℝ)) (q :=
      (20188628247545629 / 20000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

end Zeta5Irrational
end
