@[expose] public section

namespace FrobeniusTwistedLine

open scoped TensorProduct

noncomputable section

universe u v

/-- The coordinate ring `L[W, X] / (W ^ p)` of a line with its order-`p` infinitesimal
thickening. Coordinate `0` is `W` and coordinate `1` is `X`. -/
abbrev ThickenedLineCoordinateRing (L : Type v) [CommRing L] (p : ℕ) :=
  MvPolynomial (Fin 2) L ⧸ Ideal.span {thickenedLineEquation L p}

end
end FrobeniusTwistedLine
end
