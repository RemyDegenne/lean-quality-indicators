@[expose] public section

open Finset

namespace Zeta5Irrational

lemma tc_557 :
    ∀ t,
      (40654048209613 / 64000000000000 : ℝ) ≤ t →
        t ≤ (814456816291 / 1280000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_558 V_557
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

end Zeta5Irrational
end
