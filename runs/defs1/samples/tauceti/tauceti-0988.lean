public section

noncomputable section

namespace TauCeti

universe u v

variable {k : Type u} {R : Type v} [CommSemiring k] [Semiring R] [Algebra k R]

namespace OreExtension

variable {σ : R →ₐ[k] R} {δ : SigmaDerivation σ}

/-- The constant Ore polynomial. -/
def C : R →ₗ[k] OreExtension σ δ := monomial 0

end OreExtension
end TauCeti
end
end
