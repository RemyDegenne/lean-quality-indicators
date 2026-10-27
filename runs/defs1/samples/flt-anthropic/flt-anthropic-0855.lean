namespace P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero

set_option autoImplicit false

noncomputable section

namespace CharpS10bB

namespace Model

p2m_open

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*} [Field k]
  (red : A →+* k)

attribute [local instance] valuationRing_toSubring

section KerFin

abbrev algFinAlgebra : Algebra (Polynomial A) (BFin N A) := (algFin N A).toAlgebra

end KerFin
end Model
end CharpS10bB
end
end P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero
