namespace P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero

set_option autoImplicit false

noncomputable section

namespace CharpS10bB

namespace Model

p2m_open

variable (N : ℕ) [NeZero N]

variable (A : ValuationSubring (AlgebraicClosure ℚ))

section Generic

variable {L : Type*} [Field L] (A' : Subring L) {k : Type*} [Field k] (red' : A' →+* k)

theorem coeffRed_jqModC :
    coeffRed A' red' ⟨jqModC L, jqModC_mem_integralCoeffs A'⟩ = jqModC k := by
  ext n
  rw [coeffRed_coeff]
  have hL : (jqModC L).coeff n = (((jqModC ℤ).coeff n : ℤ) : L) := by
    rw [jqModC_eq_map_intCast (K := L), HahnSeries.map_coeff]
    rfl
  have hk : (jqModC k).coeff n = (((jqModC ℤ).coeff n : ℤ) : k) := by
    rw [jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff]
    rfl
  rw [hk]
  exact red_eq_intCast_of_coe_eq A' red' hL

end Generic
end Model
end CharpS10bB
end
end P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero
