public section

open groupCohomology

universe u v w

namespace TauCeti

variable (K : Type u) [CommSemiring K] (L : Type v) [CommRing L] [Algebra K L]

variable {K L}

namespace CrossedProduct

variable (c : TwoCocycle K L)

/-- The `L`-basis `u_σ` of the crossed product, indexed by `L ≃ₐ[K] L`. -/
noncomputable def basis : Module.Basis (L ≃ₐ[K] L) L (CrossedProduct c) :=
  .ofRepr ((equivFinsupp c).linearEquiv L)

end CrossedProduct
end TauCeti
end
