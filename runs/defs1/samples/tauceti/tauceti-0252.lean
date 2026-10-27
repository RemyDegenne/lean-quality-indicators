public section

open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace ClosedSubgroupConjClasses

variable [SeparatelyContinuousMul G]

/-- The conjugacy class of a closed subgroup. -/
def mk (H : ClosedSubgroup G) : ClosedSubgroupConjClasses G :=
  Quotient.mk _ H

end ClosedSubgroupConjClasses
end TauCeti
end
