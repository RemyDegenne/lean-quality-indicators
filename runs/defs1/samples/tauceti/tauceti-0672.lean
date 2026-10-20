@[expose] public section

open scoped TensorProduct

namespace TauCeti

universe u v w x y z

namespace Comodule

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}

variable [CommSemiring R]

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid M] [Module R M] [Comodule R C M]

variable [AddCommMonoid N] [Module R N]

variable {P : Type y} [AddCommMonoid P] [Module R P]

variable {M' : Type y} {N' : Type z}

variable [AddCommMonoid M'] [Module R M'] [Comodule R C M']

variable [AddCommMonoid N'] [Module R N']

/-- Transport a comodule morphism across linear equivalences on source and target. -/
def transportHom (eM : M ≃ₗ[R] N) (eN : M' ≃ₗ[R] N') (f : Hom R C M M') :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) eM
    letI : Comodule R C N' := Transport (R := R) (C := C) (M := M') (N := N') eN
    Hom R C N N' := by
  letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) eM
  letI : Comodule R C N' := Transport (R := R) (C := C) (M := M') (N := N') eN
  exact
    { toLinearMap := eN.toLinearMap ∘ₗ f.toLinearMap ∘ₗ eM.symm.toLinearMap
      map_coact := by
        ext n
        dsimp [Transport, transportCoact]
        simp only [LinearEquiv.symm_apply_apply]
        rw [← Hom.map_coact_apply f (eM.symm n)]
        exact tensor_map_transport_conj (R := R) (C := C) (M := M) (N := N) (M' := M')
          (N' := N') eM eN f.toLinearMap (coact (R := R) (C := C) (M := M) (eM.symm n)) }

end Comodule
end TauCeti
end
