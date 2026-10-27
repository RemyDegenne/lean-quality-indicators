@[expose] public section

variable (k R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

namespace Weight

variable [LieRing.IsNilpotent L] [LinearWeights R L M] (χ : Weight R L M)

variable {R L M χ}

/-- The kernel of a weight of a Lie module with linear weights. -/
abbrev ker := LinearMap.ker (χ : L →ₗ[R] R)

end Weight
end LieModule
end
