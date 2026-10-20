namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries

open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {L : Type} [Field L] [CharZero L]

p2m_reactivate

section Auto

variable (hmM' : Nat.Coprime m M') (ξ : L) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = eq m)
  (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')

def ΦRingEquiv : KL L m M' ≃+* KL L m M' :=
  { ΦHom hmM' ξ ι₀ hι₀ γ hγ with
    invFun := ΦHom hmM' ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ)
    left_inv := ΦHom_inv_apply hmM' ξ ι₀ hι₀ γ hγ
    right_inv := ΦHom_apply_inv hmM' ξ ι₀ hι₀ γ hγ }

end Auto
end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
