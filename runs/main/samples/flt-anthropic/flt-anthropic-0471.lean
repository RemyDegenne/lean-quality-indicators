namespace P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong

attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField

set_option autoImplicit false

universe u v w

p2m_open

namespace AlgebraicGeometry

namespace RelPicard

namespace LFP

p2m_open

section OneChart

variable {k : Type*} [CommRing k] {A' : Type*} [CommRing A'] [Algebra k A']
  {Γ : Type*} [CommRing Γ] [Algebra k Γ] {Γ' : Type*} [CommRing Γ'] [Algebra A' Γ']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {P' : Type*} [AddCommGroup P'] [Module Γ P'] [Module k P'] [IsScalarTower k Γ P']
  {Q : Type*} [AddCommGroup Q] [Module Γ' Q] [Module A' Q] [IsScalarTower A' Γ' Q]
  {Q' : Type*} [AddCommGroup Q'] [Module Γ' Q'] [Module A' Q'] [IsScalarTower A' Γ' Q']

theorem apply_actR_of_semilinear (φ : Γ → Γ') (β : A' ⊗[k] P ≃ₗ[A'] Q)
    (hs : ∀ (s : Γ) (m : P), β ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β ((1 : A') ⊗ₜ[k] m))
    (s : Γ) (x : A' ⊗[k] P) : β (actR k A' s x) = φ s • β x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [actR_tmul, tmul_eq_smul_one_tmul k A' a (s • m), map_smul, hs, tmul_eq_smul_one_tmul k A' a m,
      map_smul, smul_comm_of_tower]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

end OneChart
end LFP
end RelPicard
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong
