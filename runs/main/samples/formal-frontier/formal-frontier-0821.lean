set_option warningAsError true

@[expose] public section

open scoped BigOperators

namespace IsLocalRing

universe u

@[simp]
theorem nonunitsAddSubmonoid_eq_bot (K : Type u) [DivisionSemiring K] :
    nonunitsAddSubmonoid K = ⊥ := by
  apply AddSubmonoid.ext
  intro x
  change x ∈ nonunits K ↔ x ∈ (⊥ : AddSubmonoid K)
  simpa only [AddSubmonoid.mem_bot, isUnit_iff_ne_zero, not_not] using
    (mem_nonunits_iff (α := K) (a := x))

end IsLocalRing
end
