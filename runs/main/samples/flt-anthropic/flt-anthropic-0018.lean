namespace P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul

set_option autoImplicit false

open scoped MatrixGroups ModularForm

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace Conj6

open ModularCurve

section NonVanish

theorem comp_heckeDiag_ne_zero (p : ℕ) (hp : p ≠ 0) (F : UpperHalfPlane → ℂ) (hF : F ≠ 0) :
    (fun τ : UpperHalfPlane => F (ModularForm.heckeDiagMatrix p • τ)) ≠ 0 := by
  intro h
  apply hF
  funext τ
  let τ' : UpperHalfPlane := ⟨(τ : ℂ) / p, by
    rw [Complex.div_natCast_im]; exact div_pos τ.im_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp))⟩
  have hτ : ModularForm.heckeDiagMatrix p • τ' = τ := by
    apply UpperHalfPlane.ext
    rw [ModularForm.coe_heckeDiagMatrix_smul hp]
    show (p : ℂ) * ((τ : ℂ) / p) = τ
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hp)]
  have := congrFun h τ'
  rw [hτ] at this
  simpa using this

end NonVanish
end Conj6
end P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul
