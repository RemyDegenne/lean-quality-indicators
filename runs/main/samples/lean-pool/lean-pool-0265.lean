public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace Core

section

open scoped BigOperators

open Matrix

theorem effectiveConstructionAInstance_solution_coset
    (H : BinaryAffineSystem)
    (hconsistent : H.effectiveReducedConsistent = true)
    (z : Fin H.dimension → ℤ) :
    H.Solves (H.effectiveAffineRepresentative - z) ↔
      ∃ coefficients : Fin H.dimension → ℤ,
        H.effectiveSquareBasisMatrix.mulVec coefficients = z := by
  rw [H.solves_sub_iff_inLattice
    (H.effectiveAffineRepresentative_solves hconsistent)]
  exact H.inLattice_iff_exists_effectiveSquareBasisMatrix z

end
end Core
end GapCVP
end
end
