namespace P2MW.S_ModularCurve_PDPairing_index_Gamma_four

set_option autoImplicit false

open scoped MatrixGroups

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace ModularCurve

namespace PDPairing

namespace TD

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Rows

open MulAction

def IsPar (Φ : Subgroup SL(2, ℤ)) {A : Type*} [AddCommGroup A] (φ : Additive Φ →+ A) : Prop :=
  ∀ γ : Φ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0

end Rows
end TD
end PDPairing
end ModularCurve
end P2MW.S_ModularCurve_PDPairing_index_Gamma_four
