set_option autoImplicit false

open groupCohomology

namespace HeckeCohomology

variable {k Γ : Type} [CommRing k] [Group Γ] (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) (A : Rep k Γ)

def IsTwist (φ : A →ₗ[k] A) : Prop := ∀ (s : S₂) (a : A), φ (A.ρ (c s : Γ) a) = A.ρ (s : Γ) (φ a)

end HeckeCohomology
