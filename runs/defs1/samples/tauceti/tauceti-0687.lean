public section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra TauCeti.QuadraticMap

open Module Filter

open scoped TensorProduct Topology

noncomputable section

variable {p : ℕ} [Fact p.Prime] {V ι : Type*}
  [AddCommGroup V] [Module ℚ_[p] V] [Fintype ι] [DecidableEq ι]
  (Q : QuadraticForm ℚ_[p] V) (b : Basis ι ℚ_[p] V)

/-- Spin points whose orthogonal actions and inverse actions are integral in the basis `b`.
This is the full preimage of the integral orthogonal subgroup under the Spin projection. -/
def integralSpinSubgroup : Subgroup (spinGroup Q) :=
  (integralOrthogonalSubgroup Q b).comap (spinToOrthogonal Q)

end
end TauCeti.CliffordAlgebra
end
