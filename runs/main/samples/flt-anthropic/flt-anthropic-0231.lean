namespace P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open PowerSeries Polynomial Filter Topology

namespace CuspDisc

section Ultra

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

theorem Bdd.mul_small {ρ C C' : ℝ} {m : ℕ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hC' : 0 ≤ C') (hP : Bdd C P) (hQ : Small ρ C' m Q) : Small ρ (C * C') m (P * Q) := by
  rw [mul_comm P Q, mul_comm C C']
  exact hQ.mul hρ0 hρ1 hC' hC hP

end Ultra
end CuspDisc
end
end P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le
