@[expose] public section

open Set TopologicalSpace

variable {α : Type*}

namespace Topology

section Lawson

namespace WithLawson

/-- `ofLawson` is the identity function from the `WithLawson` of a type. -/
@[match_pattern] def ofLawson : WithLawson α ≃ α := Equiv.refl _

end WithLawson
end Lawson
end Topology
end
