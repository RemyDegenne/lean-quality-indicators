namespace P2MW.S_jacobiTheta_two_eq_tprod

set_option autoImplicit false

noncomputable section

namespace JTPEngine

open Finset

theorem qfact_succ (Q : ℂ) (m : ℕ) : qfact Q (m + 1) = qfact Q m * (1 - Q ^ (m + 1)) := by
  unfold qfact
  exact Finset.prod_range_succ _ m

end JTPEngine
end
end P2MW.S_jacobiTheta_two_eq_tprod
