@[expose] public section

open Finset

namespace Zeta5Irrational

lemma tc_247 :
    ∀ t,
      (6742465461111 / 32000000000000 : ℝ) ≤ t →
        t ≤ (3388292789099 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_248 V_247
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

end Zeta5Irrational
end
