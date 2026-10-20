public section

open WithConv

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x y

variable {R : Type u} {H : Type v} {M : Type w} {N : Type x}

variable [CommSemiring R]

variable [AddCommMonoid M] [Module R M]

variable [AddCommMonoid N] [Module R N]

variable [Module.Finite R M] [Module.Projective R M]

noncomputable section

attribute [local instance] dual tensor

section Hom

variable [Semiring H] [HopfAlgebra R H] [Comodule R H M] [Comodule R H N]

/-- The comodule of linear maps from a finite projective comodule to an arbitrary comodule,
with the contragredient action on the source. This is an explicit structure, not a global
instance, so different coactions on the same linear Hom space can coexist. -/
@[implicit_reducible]
def linearHom : Comodule R H (M →ₗ[R] N) :=
  Transport (C := H) (dualTensorHomEquiv R M N)

end Hom
end
end TauCeti.Comodule
end
