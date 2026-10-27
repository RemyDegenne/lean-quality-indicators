namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_two

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

def τEquiv : KL L m M' ≃ₐ[L] KL L m M' :=
  AlgEquiv.ofRingEquiv (f := ΦRingEquiv hmM' ξ ι₀ hι₀ γ hγ) (ΦHom_algebraMap hmM' ξ ι₀ hι₀ γ hγ)

end Auto
end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_two
