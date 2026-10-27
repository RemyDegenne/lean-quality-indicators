public section

namespace TauCeti

open PathAlgebra DoubledQuiver

variable (k : Type*) [Field k] {V : Type*} (G : SimpleGraph V) [Finite V]

local notation "Z" => nonisolatedZigzagQuotient k G

/-- The endpoint of the paths in a quadratic relation, hence the vertex of its projective. -/
abbrev ZigzagQuadraticRelationIndex.vertex {i : V} : ZigzagQuadraticRelationIndex G i → V
  | .inl r => r.2.1.1
  | .inr _ => i

end TauCeti
end
