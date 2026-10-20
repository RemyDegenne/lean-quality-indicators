public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllObj

variable {B : Scheme.{u}}

/-- An **arrow of `Ell/B`** from `X = (S', E')` to `Y = (S, E)`: a morphism of `B`-schemes
`base : S' ⟶ S` and a morphism `total : E' ⟶ E` of total spaces such that the square formed by
`total`, `base` and the two structure morphisms is cartesian, and carrying the zero section of `E'`
to that of `E`. It exhibits `E'` as the base change of `E` along `base`. -/
structure Hom (X Y : EllObj B) where
  /-- The morphism of bases. -/
  base : X.base ⟶ Y.base
  /-- The morphism of bases is a morphism of `B`-schemes. -/
  base_structureMap : base ≫ Y.structureMap = X.structureMap
  /-- The morphism of total spaces. -/
  total : X.curve.carrier ⟶ Y.curve.carrier
  /-- The square formed by `total`, `base` and the structure morphisms is cartesian. -/
  isPullback : IsPullback total X.curve.structureMap Y.curve.structureMap base
  /-- The morphism of total spaces carries the zero section to the zero section. -/
  zero_total : X.curve.zero ≫ total = base ≫ Y.curve.zero

end EllObj
end TauCeti.AlgebraicGeometry
end
