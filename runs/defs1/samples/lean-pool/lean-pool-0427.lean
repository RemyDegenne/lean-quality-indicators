universe u v

open scoped DirectSum

public noncomputable section

namespace LoweringDerivation

variable {E : Type u} {R : Type v} [Field E] [CommRing R] [Algebra E R]

variable (𝒜 : NatOrdinal → Submodule E R) [GradedAlgebra 𝒜]

/-- The quotient `A/I`, `I = I_{≥1}`; for `A = P̂` the paper's `P̂/I`. -/
abbrev Fibre : Type v := R ⧸ fibreIdeal 𝒜

end LoweringDerivation
end
