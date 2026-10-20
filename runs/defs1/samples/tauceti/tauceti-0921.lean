public section

open PowerSeries

namespace TauCeti

namespace FormalCoordinate

variable {R : Type*} [CommRing R]

section Field

variable {K : Type*} [Field K]

variable (K) in
/-- Over a field, `φ ↦ σ_φ` is an isomorphism between the group of formal coordinates and the
opposite of the automorphism group of `K⟦X⟧`, with inverse `σ ↦ σ X`. -/
noncomputable def substAlgEquivMulEquiv : FormalCoordinate K ≃* (K⟦X⟧ ≃ₐ[K] K⟦X⟧)ᵐᵒᵖ where
  __ := substAlgEquivHom
  invFun σ := ofAlgEquiv σ.unop
  left_inv := ofAlgEquiv_substAlgEquiv
  right_inv σ := MulOpposite.unop_injective (substAlgEquiv_ofAlgEquiv σ.unop)

end Field
end FormalCoordinate
end TauCeti
end
