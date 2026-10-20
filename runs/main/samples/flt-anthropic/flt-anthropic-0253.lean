namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_levelAut_eq_one_of_map_eq_one_or_eq_neg_one_of_exists_ringHom

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

theorem ΦHom_apply_inv (X : KL L m M') :
    ΦHom hmM' ξ ι₀ hι₀ γ hγ (ΦHom hmM' ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ) X) = X := by
  apply Subtype.ext
  refine Φfun_eq hmM' ξ ι₀ hι₀ γ hγ ?_
  exact ((isImgC_ΦHom hmM' ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ) X).symm
    (isImgC_ΦHom hmM' ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ) (ΦHom hmM' ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ) X)).hasRep).congr_γ
    (inv_inv γ)

end Auto
end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_AuxLevel_levelAut_eq_one_of_map_eq_one_or_eq_neg_one_of_exists_ringHom
