public section

namespace CFSG.ClassicalInvolution.GlaubermanAut

open SemidirectProduct CFSG.ABGLocalTools

section ZStarStep

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {A : Subgroup (MulAut G)}

omit [Finite G] in
theorem conj_inl_inr_inl (x : G) (τ : A) :
    (inl x : AutExt A) * inr τ * (inl x)⁻¹ * (inr τ)⁻¹ = inl (x * (τ : MulAut G) x⁻¹) := by
  have h := inl_aut (φ := A.subtype) τ x⁻¹
  have h2 : (inr τ : AutExt A) * inl x⁻¹ * (inr τ)⁻¹ = inl ((τ : MulAut G) x⁻¹) := by
    rw [← map_inv]
    exact h.symm
  calc (inl x : AutExt A) * inr τ * (inl x)⁻¹ * (inr τ)⁻¹
      = inl x * ((inr τ : AutExt A) * inl x⁻¹ * (inr τ)⁻¹) := by rw [← map_inv]; group
    _ = inl (x * (τ : MulAut G) x⁻¹) := by rw [h2, ← map_mul]

end ZStarStep
end CFSG.ClassicalInvolution.GlaubermanAut
end
