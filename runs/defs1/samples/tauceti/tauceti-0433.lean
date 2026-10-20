public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

variable (μ : R)

variable {W : WeierstrassCurve R} {x₁ y₁ x₂ y₂ : R}

variable (h : W.IsThreeTorsionBasis x₁ y₁ x₂ y₂)

namespace UniversalLevelThree

open MvPolynomial (X)

/-- The ring `ℤ[μ, ζ] / (ζ² + ζ + 1)`, with `μ = X 0` and `ζ = X 1`. -/
abbrev PolyRing : Type :=
  MvPolynomial (Fin 2) ℤ ⧸ Ideal.span {(X 1 ^ 2 + X 1 + 1 : MvPolynomial (Fin 2) ℤ)}

end UniversalLevelThree
end WeierstrassCurve
end
