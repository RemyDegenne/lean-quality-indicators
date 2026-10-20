@[expose] public section

namespace Utilities.Certificate.DiscreteSpecialization

open Finset ExplicitPotential SubdivisionGraph DegenerateSpec

open ContractionForestCensusGeneral

open Utilities.Subdivision.SubdivisionCoreSupport

variable {n p : ℕ}

theorem coreClassDivisor_subChipWeight (d : DegSpec n p)
    (weight : Fin n → ℤ) (anchor : Fin n) :
    d.coreClassDivisor (subChipWeight weight anchor) =
      d.coreClassDivisor weight - oneChip (d.coreVertex anchor) := by
  classical
  funext x
  rcases x with c | interior
  · simp [DegSpec.coreClassDivisor, subChipWeight, Finset.sum_sub_distrib,
      oneChip, DegSpec.coreVertex, Subtype.ext_iff, eq_comm]
  · simp [DegSpec.coreClassDivisor, oneChip, DegSpec.coreVertex]

end Utilities.Certificate.DiscreteSpecialization
end
