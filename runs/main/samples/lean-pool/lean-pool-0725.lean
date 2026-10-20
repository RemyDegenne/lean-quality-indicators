@[expose] public section

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm EisensteinSeries

open scoped Real ComplexOrder Manifold MatrixGroups

lemma modularForm_SL_smul {k : ℤ} (f : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = (denom γ τ) ^ k * f τ := by
  have h0 : (⇑f) ∣[k] γ = ⇑f :=
    f.slash_action_eq' _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)
  have h := congr_fun h0 τ
  rw [SL_slash_apply, zpow_neg, ← div_eq_mul_inv,
    div_eq_iff (zpow_ne_zero k (denom_ne_zero γ τ))] at h
  rw [h, mul_comm]

end Chudnovsky
end
end
