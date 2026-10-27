public section

open CategoryTheory

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace FGComoduleCat

variable (R : Type u) (C : Type v)

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable {M : Type w} [AddCommMonoid M] [Module R M] [Module.Finite R (M ⊗[R] C)]

variable {N : Type w} [AddCommMonoid N] [Module R N] [Module.Finite R (N ⊗[R] C)]

attribute [local instance] Comodule.cofree

variable {P : FGComoduleCat.{u, v, max w v} R C}

/-- The finite-category cofree lift of an `R`-linear map from a finite comodule to the
coefficient module. -/
noncomputable abbrev cofreeLift (P : FGComoduleCat.{u, v, max w v} R C) (g : P →ₗ[R] M) :
    P ⟶ cofree (R := R) (C := C) M :=
  ObjectProperty.homMk
    (ComoduleCat.ofHom (R := R) (C := C) (Comodule.Hom.cofreeLift (C := C) g))

end FGComoduleCat
end TauCeti
end
