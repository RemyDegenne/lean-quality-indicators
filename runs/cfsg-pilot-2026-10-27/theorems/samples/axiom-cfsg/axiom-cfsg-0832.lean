public section

namespace CFSG.StandardType.ZS

theorem wSlpmC_glue_conj_of {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a b : U) (α β : U →ₗ[ZMod p] ZMod p) (hα : α a = 2)
    (hβ : β b = 2) (h2 : (2 : ZMod p) ≠ 0) (r s : U ≃ₗ[ZMod p] U)
    (hr : ∀ v, r v = v - α v • a) (hs : ∀ v, s v = v - β v • b)
    (e : ↥(LinearMap.ker α) ≃ₗ[ZMod p] ↥(LinearMap.ker β)) :
    wSlpmC_glue a α hα h2 b β hβ e * r * (wSlpmC_glue a α hα h2 b β hβ e)⁻¹ = s := by
  have h : wSlpmC_glue a α hα h2 b β hβ e * r =
      s * wSlpmC_glue a α hα h2 b β hβ e := by
    ext z
    rcases (wSlpmC_Ea a α hα h2).surjective z with ⟨⟨x, y⟩, rfl⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, wSlpmC_of_refl_Ea hα h2 r hr,
      wSlpmC_glue_apply, wSlpmC_glue_apply, wSlpmC_of_refl_Ea hβ h2 s hs, map_neg]
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.StandardType.ZS
end
