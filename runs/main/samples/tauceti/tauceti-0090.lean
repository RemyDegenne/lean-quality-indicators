public section

namespace TauCeti

open _root_.Quiver MulOpposite

universe u v w

namespace PathAlgebra

section Dual

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q]
  (R : Submodule k (pathAlgebra k Q))

variable {k Q R}

variable (k Q R) [Finite Q]

theorem quadraticDualMk_apply [∀ a b : Q, Finite (a ⟶ b)]
    (f : (pathAlgebra k Q)ᵐᵒᵖ) :
    quadraticDualMk k Q R f = Ideal.Quotient.mk (quadraticDualIdeal k Q R).asIdeal f := by
  rw [quadraticDualMk, Ideal.Quotient.mkₐ_eq_mk]

end Dual
end PathAlgebra
end TauCeti
end
