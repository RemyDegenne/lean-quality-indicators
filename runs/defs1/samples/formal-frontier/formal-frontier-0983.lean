public section

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The coordinate ring cut out by the `N`-th power of the additive coordinate. -/
abbrev additivePowerCoordinateRing (K : Type u) [CommRing K] (N : ℕ) :=
  additiveGroupCoordinateRing K ⧸ additivePowerIdeal K N

end AlgebraicGeometry
end
end
