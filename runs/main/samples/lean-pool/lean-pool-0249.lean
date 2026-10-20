@[expose] public section

open Finset

namespace Zeta5Irrational

lemma tc_361 :
    ∀ t,
      (46687825988961 / 128000000000000 : ℝ) ≤ t →
        t ≤ (2338577156961 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_362 V_361
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

end Zeta5Irrational
end
