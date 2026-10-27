public section

open CategoryTheory Representation

namespace TauCeti

universe u v v' w w'

section Linear

variable {k : Type u} {G : Type v} {H : Type v'} [CommSemiring k] [Group G] [Group H] (φ : G →* H)
  {A : Type w} {B : Type w'} [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
  (ρ : Representation k G A) (τ : Representation k H B)

/-- The dual projection formula as a `k`-linear equivalence of the underlying modules: the two maps
above are mutually inverse because `τ h` and `τ h⁻¹` cancel. -/
noncomputable def coindProjectionLEquiv :
    coindV φ (linHom (τ.comp φ) ρ) ≃ₗ[k] B →ₗ[k] coindV φ ρ :=
  LinearEquiv.ofLinearMap (coindProjectionHom φ ρ τ) (coindProjectionInv φ ρ τ)
    (by ext Φ b h; simp)
    (by ext F h b; simp)

end Linear
end TauCeti
end
