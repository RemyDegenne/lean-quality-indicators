@[expose] public section

open Finset

namespace Zeta5Irrational

lemma tc_442 :
    ∀ t,
      (1858305405063 / 4000000000000 : ℝ) ≤ t →
        t ≤ (116309625301 / 250000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_443 V_442
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

end Zeta5Irrational
end
