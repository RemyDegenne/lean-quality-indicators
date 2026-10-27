public section

open scoped TensorProduct

open CategoryTheory

namespace TauCeti

namespace Comodule

attribute [local simp] TensorProduct.AlgebraTensorModule.map_eq
  TensorProduct.AlgebraTensorModule.assoc_eq

variable {R H M N P : Type*} [CommSemiring R] [CommSemiring H] [Bialgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M]
  [AddCommMonoid N] [Module R N] [Comodule R H N]
  [AddCommMonoid P] [Module R P] [Comodule R H P]

attribute [local instance] symmetricAlgebra

namespace Hom

variable (R H M) in
/-- The inclusion `ι : M → SymmetricAlgebra R M` of generators, as a comodule morphism. -/
noncomputable def symmetricAlgebraι : Hom R H M (SymmetricAlgebra R M) where
  toLinearMap := SymmetricAlgebra.ι R M
  map_coact := by
    ext m
    simp [LinearMap.rTensor_def]

end Hom
end Comodule
end TauCeti
end
