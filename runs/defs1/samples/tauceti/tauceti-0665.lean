public section

namespace TauCeti

open Finset

variable {n : ℕ}

/-- The **numerator of the Weyl dimension formula**: the product `∏_{i < j} (λᵢ - λⱼ + j - i)` of
the differences of `TauCeti.DominantWeight.rhoShift`. -/
def weylDimensionNumerator (l : DominantWeight n) : ℤ :=
  ∏ i, ∏ j ∈ Ioi i, (l.rhoShift i - l.rhoShift j)

end TauCeti
end
