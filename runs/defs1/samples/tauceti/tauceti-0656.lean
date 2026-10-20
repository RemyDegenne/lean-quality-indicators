public section

universe u

section RelativeModuli

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj WeierstrassCurve UniversalTate

namespace TauCeti.AlgebraicGeometry

namespace EllObj

variable {B : Scheme.{u}} {N : ℕ} {hN : ∀ b : B, (N : B.residueField b) ≠ 0}

/-- The scheme `Z` of points of naive exact order `N` of an object `X = (E/S)` of `Ell/B`, as a
scheme over `S`: the open subscheme `naiveExactOrderOpens` of the `N`-torsion `E[N]`. It is finite
étale over `S`. -/
noncomputable abbrev naiveExactOrderOver (X : EllObj B)
    (hN : ∀ s : X.base, (N : X.base.residueField s) ≠ 0) : Over X.base :=
  Over.mk ((X.curve.naiveExactOrderOpens hN).ι ≫ (X.curve.torsion N).X.hom)

end EllObj
end TauCeti.AlgebraicGeometry
end RelativeModuli
end
