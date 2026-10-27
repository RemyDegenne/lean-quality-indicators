@[expose] public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}

variable [CommSemiring R]

variable [AddCommMonoid M] [Module R M]

variable [AddCommMonoid N] [Module R N]

section TrivialDef

variable [Semiring C] [Bialgebra R C]

section Trivial

attribute [local instance] trivial

/-- A linear map between trivial comodules is automatically a comodule morphism. -/
def Hom.ofTrivial (f : M →ₗ[R] N) : Hom R C M N :=
  Hom.ofGroupLike (R := R) (C := C) (M := M) (N := N) (1 : GroupLike R C) f

end Trivial
end TrivialDef
end Comodule
end TauCeti
end
