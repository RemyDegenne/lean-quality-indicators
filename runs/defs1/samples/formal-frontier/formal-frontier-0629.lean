@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

set_option linter.mathlibStandardSet true

set_option linter.style.header false

noncomputable section

open Polynomial

namespace QuadraticAlgebra

universe u

variable {R : Type u} [Field R]

variable [IsRealClosed R]

/-- The quotient by any irreducible nonlinear polynomial over a real-closed
field is algebra-equivalent to its canonical quadratic field. The choice of
root fixes the map but is not part of the caller's hypotheses. -/
noncomputable def adjoinRootEquivOfIrreducible (p : R[X]) (hp : Irreducible p)
    (hdeg : 1 < p.natDegree) :
    AdjoinRoot p ≃ₐ[R] QuadraticAlgebra R (-1) 0 :=
  adjoinRootEquivOfRoot p hp
    (Nat.le_antisymm (IsRealClosed.irreducible_natDegree_le_two hp)
      (Nat.succ_le_of_lt hdeg)) (rootOfIrreducible p hp)
    (rootOfIrreducible_aeval p hp)

end QuadraticAlgebra
end
end
