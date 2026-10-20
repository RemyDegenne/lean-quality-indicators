namespace P2MW.S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace ModularCurve

namespace CupPairing

namespace Shapiro

p2m_open

open Matrix.SpecialLinearGroup ModularGroup MulAction

open scoped MatrixGroups

section Main

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)

variable (f : SL(2, ℤ) ⧸ Γ → ℤ)

variable {Γ f} (P : Potentials Γ f)

theorem b_mul (g : SL(2, ℤ)) (γ : Γ) : P.b (g * γ) = P.b g + phi P (Additive.ofMul γ) := by
  rw [phi_apply, ← b_mul_sub_eq P γ γ.2 g]; ring

end Main
end Shapiro
end CupPairing
end ModularCurve
end P2MW.S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero
