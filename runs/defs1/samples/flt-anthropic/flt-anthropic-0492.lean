namespace P2MW.S_CartierDual_exists_algEquiv_monoidAlgebra_pi

set_option autoImplicit false

open scoped TensorProduct

namespace P2mS17E

variable (R : Type*) [CommRing R] (Γ : Type*) [CommGroup Γ] [Fintype Γ]

noncomputable def evalAlgEquiv : CartierDual R (MonoidAlgebra R Γ) ≃ₐ[R] (Γ → R) :=
  AlgEquiv.ofLinearEquiv (evalEquiv R Γ) (evalEquiv_one R Γ) (evalEquiv_mul R Γ)

end P2mS17E
end P2MW.S_CartierDual_exists_algEquiv_monoidAlgebra_pi
