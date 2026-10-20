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

section SymmetricPower

variable (R H M) in
/-- The degree-`n` homogeneous piece as a subcomodule of the symmetric algebra. -/
noncomputable def symmetricPowerSubcomodule (n : ℕ) : Subcomodule R H (SymmetricAlgebra R M) :=
  Subcomodule.ofSubmodule (SymmetricAlgebra.homogeneousSubmodule R M n) fun _ hx ↦ by
    rw [symmetricAlgebra_coact, AlgHom.toLinearMap_apply, ← LinearMap.rTensor_def,
      ← DirectSum.decomposeTensor_apply]
    exact symmetricAlgebraCoact_mem_decomposeTensor hx

end SymmetricPower
end Comodule
end TauCeti
end
