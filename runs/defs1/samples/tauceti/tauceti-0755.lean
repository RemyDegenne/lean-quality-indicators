public section

open CategoryTheory WithConv

open scoped DirectSum TensorProduct

namespace Derivation

open TauCeti

attribute [local instance] Classical.decEq

attribute [local instance] adjointComodule

universe u v w

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]

variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

variable {M : Type w} [CommGroup M]

section Transport

variable {R H L M : Type u} [CommRing R] [CommRing H] [CommRing L] [HopfAlgebra R H]
  [HopfAlgebra R L] [CommGroup M]

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]
  [Module.Finite R (Bialgebra.CotangentSpace R L)]
  [Module.Projective R (Bialgebra.CotangentSpace R L)]

/-- A bijective differential restricts to a linear equivalence of corresponding adjoint
weight spaces. -/
noncomputable def _root_.BialgHom.adjointWeightSpaceEquivOfBijective (φ : H →ₐc[R] L)
    (hφ : Function.Bijective (dualCotangentMap φ)) (π : L →ₐc[R] MonoidAlgebra R M) (α : M) :
    adjointWeightSpace π α ≃ₗ[R] adjointWeightSpace (π.comp φ) α :=
  ((LinearEquiv.ofBijective (dualCotangentMap φ) hφ).submoduleMap
    (adjointWeightSpace π α)).trans
      (LinearEquiv.ofEq _ _ (by
        rw [ofBijective_dualCotangentMap_toLinearMap φ hφ]
        exact φ.map_dualCotangentMap_adjointWeightSpace_of_bijective hφ π α))

end Transport
end Derivation
end
