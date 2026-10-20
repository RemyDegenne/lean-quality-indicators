@[expose] public section

namespace PowerSeries

open WithPiTopology

variable {R : Type*} [CommRing R]

variable {S : Type*} [CommRing S]

variable {φ : R →+* S}

section

variable [TopologicalSpace R] [TopologicalSpace S]

variable [IsTopologicalRing S] [IsLinearTopology S S]

/-- The domain of evaluation of `MvPowerSeries`, as an ideal -/
@[simps]
def hasEvalIdeal : Ideal S where
  carrier := {a | HasEval a}
  add_mem' := HasEval.add
  zero_mem' := HasEval.zero
  smul_mem' := HasEval.mul_left

end
end PowerSeries
end
