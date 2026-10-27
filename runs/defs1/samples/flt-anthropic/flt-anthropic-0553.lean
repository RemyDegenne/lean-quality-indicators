namespace P2MW.S_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker

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

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {ℓg : ℕ} {H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ} {L : Type} [Field L] [CharZero L]

p2m_reactivate

section Auto

variable (hmM' : Hyp m M' ℓg H₁) (ξ : L) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = eq m)
  (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')

def ΦHom : KL L m M' H₁ →+* KL L m M' H₁ where
  toFun := Φfun hmM' ξ ι₀ hι₀ γ hγ
  map_one' := Subtype.ext (Φfun_eq hmM' ξ ι₀ hι₀ γ hγ (by
    simp only [OneMemClass.coe_one, map_one]; exact IsImgC.one))
  map_mul' X Y := Subtype.ext (Φfun_eq hmM' ξ ι₀ hι₀ γ hγ (by
    simp only [MulMemClass.coe_mul, map_mul]
    exact (isImgC_Φfun hmM' ξ ι₀ hι₀ γ hγ X).mul (isImgC_Φfun hmM' ξ ι₀ hι₀ γ hγ Y)))
  map_zero' := Subtype.ext (Φfun_eq hmM' ξ ι₀ hι₀ γ hγ (by
    simp only [ZeroMemClass.coe_zero, map_zero]; exact IsImgC.zero))
  map_add' X Y := Subtype.ext (Φfun_eq hmM' ξ ι₀ hι₀ γ hγ (by
    simp only [AddMemClass.coe_add, map_add]
    exact (isImgC_Φfun hmM' ξ ι₀ hι₀ γ hγ X).add (isImgC_Φfun hmM' ξ ι₀ hι₀ γ hγ Y)))

end Auto
end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker
