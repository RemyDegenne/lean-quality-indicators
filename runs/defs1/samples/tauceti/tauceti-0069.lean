public section

namespace TauCeti

open _root_.Quiver MulOpposite PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) {V : Type u} (G : SimpleGraph V)

variable [CommRing k]

/-- The **quadratic relation space of a zigzag algebra**: the `k`-span of the quadratic zigzag
relators inside the degree-two part of the path algebra of the doubled quiver. -/
noncomputable def quadraticZigzagRelations : Submodule k (pathAlgebra k (DoubledQuiver G)) :=
  Submodule.span k {x | IsQuadraticZigzagRelator k G x}

end TauCeti
end
