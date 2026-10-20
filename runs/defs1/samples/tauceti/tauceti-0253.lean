public section

noncomputable section

open CategoryTheory Limits Opposite

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)]
  (M : ModuleCat.{max v w} R) {X : TopCat.{v}}

section Definition

variable (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- The singular cohomology of `X` in degree `n` with coefficients in the local coefficient
system `L` and values in `M`. -/
abbrev twistedCohomology (n : ℕ) : ModuleCat.{max v w} k :=
  (L.twistedCochainComplex k M).homology n

end Definition
end LocalCoefficientSystem
end TauCeti
end
end
