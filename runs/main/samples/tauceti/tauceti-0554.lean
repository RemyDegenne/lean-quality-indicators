public section

namespace TauCeti

open Bornology Set

variable {U : Set ℂ}

theorem hasHolomorphicSquareRoots_of_filledHull_subset (hUo : IsOpen U)
    (hUf : filledHull U ⊆ U) : HasHolomorphicSquareRoots U :=
  ⟨fun _ hg hg₀ =>
    Contour.exists_differentiableOn_pow_eq_of_filledHull_subset hUo hUf hg hg₀ two_ne_zero⟩

end TauCeti
end
