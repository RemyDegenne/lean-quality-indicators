public section

open Matrix

open scoped TensorProduct

namespace TauCeti.SpStd

open LieAlgebra.Symplectic

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

/-- The target coordinate of a numbered root generator: the coordinate carrying the image of the
basis vector at `rootSource`. -/
def rootTarget : Fin (n + 1) ⊕ Fin (n + 1) → Fin (n + 1) ⊕ Fin (n + 1)
  | .inl i => .inl i
  | .inr i => if i = Fin.last n then .inr i else .inl (Order.succ i)

end TauCeti.SpStd
end
