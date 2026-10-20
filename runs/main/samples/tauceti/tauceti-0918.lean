public section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra TauCeti.QuadraticMap

open Module Filter

open scoped TensorProduct Topology

noncomputable section

variable {p : ℕ} [Fact p.Prime] {V ι : Type*}
  [AddCommGroup V] [Module ℚ_[p] V] [Fintype ι] [DecidableEq ι]
  (Q : QuadraticForm ℚ_[p] V) (b : Basis ι ℚ_[p] V)

theorem isCompact_integralSpinSubgroup (hQ : Q.Nondegenerate) :
    IsCompact (integralSpinSubgroup Q b : Set (spinGroup Q)) := by
  let : FiniteDimensional ℚ_[p] V := Module.Finite.of_basis b
  exact isCompact_preimage_spinToOrthogonal Q hQ (isCompact_integralOrthogonalSubgroup Q b)

end
end TauCeti.CliffordAlgebra
end
