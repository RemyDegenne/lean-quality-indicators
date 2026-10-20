@[expose] public section

open Filter Set TopologicalSpace Function

open Filter Pointwise

open scoped Topology

universe u

namespace RingFilterBasis

variable {R : Type u} [Ring R] (B : RingFilterBasis R)

/-- The topology associated to a ring filter basis.
It has the given basis as a basis of neighborhoods of zero. -/
@[instance_reducible]
def topology : TopologicalSpace R :=
  B.toAddGroupFilterBasis.topology

end RingFilterBasis
end
