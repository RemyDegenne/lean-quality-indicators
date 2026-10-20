@[expose] public section

universe u v

variable {R : Type*} [CommRing R] (I : Ideal R)

variable (M : Type*) [AddCommGroup M] [Module R M]

variable {N : Type*} [AddCommGroup N] [Module R N]

open TensorProduct

namespace AdicCompletion

section Noetherian

variable {R : Type u} [CommRing R] (I : Ideal R)

variable (M : Type u) [AddCommGroup M] [Module R M]

open CategoryTheory

variable [IsNoetherianRing R]

section

variable {M : Type u} [AddCommGroup M] [Module R M]

variable {N : Type u} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)

variable [Module.Finite R M] [Module.Finite R N]

variable {f}

lemma tensor_map_id_left_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (AlgebraTensorModule.map LinearMap.id f :
        AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] N) := by
  rw [tensor_map_id_left_eq_map I f]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp]
  exact map_injective I hf

end
end Noetherian
end AdicCompletion
end
