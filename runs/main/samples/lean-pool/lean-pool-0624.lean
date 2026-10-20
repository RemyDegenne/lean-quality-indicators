@[expose] public section

open Finset

namespace Zeta5Irrational

lemma tc_336 :
    ∀ t,
      (3929638815327 / 12800000000000 : ℝ) ≤ t →
        t ≤ (616435551059 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_337 V_336
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

end Zeta5Irrational
end
