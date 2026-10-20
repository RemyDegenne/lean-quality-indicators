public section

open NormedSpace MeasureTheory

noncomputable section

namespace TauCeti

open scoped RightActions

variable {𝕂 R : Type*}

section Definitions

variable [NontriviallyNormedField 𝕂] [NormedRing R] [NormedAlgebra 𝕂 R]

/-- The sum of the Fréchet-derivative series of the Banach-algebra exponential. It converges under
the hypotheses of `summable_expFDerivTerm`; as usual for `tsum`, it has the junk value zero when
the series is not summable. -/
noncomputable def expFDeriv (𝕂 : Type*) [NontriviallyNormedField 𝕂] {R : Type*} [NormedRing R]
    [NormedAlgebra 𝕂 R] (x : R) : R →L[𝕂] R :=
  ∑' n : ℕ, expFDerivTerm 𝕂 x n

end Definitions
end TauCeti
end
end
