namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DickmanDecay

open MeasureTheory Filter

open scoped Topology

open Dickman

theorem deriv_le_of_hazard {u rate : ℝ} (hu : 1 < u) (hrate : rate ≤ hazard u) :
    deriv rho u ≤ -rate * rho u := by
  rw [hazard_eq_neg_deriv hu] at hrate
  have h := (le_div_iff₀ (rho_pos u)).mp hrate
  linarith

end NumberTheoryLean.DickmanDecay
end
end Erdos970
end OAI
