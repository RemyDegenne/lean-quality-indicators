public section

open MvPolynomial HomogeneousLocalization

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W' : Projective R) (i : Fin 3)

/-- The coordinate ring `R[X₀, X₁, X₂] ⧸ (W(X₀, X₁, X₂), Xᵢ - 1)` of the standard affine chart
`Xᵢ ≠ 0` of the projective Weierstrass cubic. -/
abbrev ChartRing : Type _ :=
  MvPolynomial (Fin 3) R ⧸ Ideal.span (Set.range (W'.chartRelation i))

end WeierstrassCurve.Projective
end
