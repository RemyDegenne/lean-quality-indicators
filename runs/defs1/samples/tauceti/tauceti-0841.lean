public section

open scoped TensorProduct

open TensorProduct

namespace TauCeti

namespace Comodule

universe u v w x y z

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}

variable [CommSemiring R]

section Structure

variable [Semiring C] [Bialgebra R C]

variable [AddCommMonoid M] [Module R M] [Comodule R C M]

variable [AddCommMonoid N] [Module R N] [Comodule R C N]

attribute [local instance] tensor

namespace Hom

variable {M' : Type y} {N' : Type z}

variable [AddCommMonoid M'] [Module R M'] [Comodule R C M']

variable [AddCommMonoid N'] [Module R N'] [Comodule R C N']

/-- The tensor product of two comodule morphisms, as a morphism of tensor-product comodules.

Both source and target carry the diagonal coaction of `Comodule.tensor`; the required
compatibility is `Comodule.tensorCoact_natural`. -/
@[expose]
noncomputable def tensorMap (f : Hom R C M M') (g : Hom R C N N') :
    Hom R C (M ⊗[R] N) (M' ⊗[R] N') where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  map_coact := tensorCoact_natural f g

end Hom
end Structure
end Comodule
end TauCeti
end
