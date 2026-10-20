@[expose] public section

noncomputable section

universe uR uM

open TensorProduct

namespace AdicCompletion

section FinitePresentation

variable {R : Type uR} [CommRing R] (I : Ideal R)

variable (M : Type uM) [AddCommGroup M] [Module R M] [hfp : Module.FinitePresentation R M]

variable (hcofinal : ∀ (n : ℕ) (K : Submodule R (Fin n → R)), K.FG →
  ∀ k : ℕ, ∃ l : ℕ, K ⊓ (I ^ l • ⊤ : Submodule R (Fin n → R)) ≤ I ^ k • K)

include hfp hcofinal

@[simp]
theorem ofTensorProductEquivOfFinitePresentation_symm_of (m : M) :
    (ofTensorProductEquivOfFinitePresentation I M hcofinal).symm (of I M m) =
      (1 : AdicCompletion I R) ⊗ₜ[R] m := by
  apply (ofTensorProductEquivOfFinitePresentation I M hcofinal).injective
  simp

end FinitePresentation
end AdicCompletion
end
end
