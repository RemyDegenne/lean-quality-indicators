@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDominantRationalScheme

/-- A dominant native quotient rational map, with a proof-only dominance field. -/
structure Hom (X Y : IntegralDominantRationalScheme.{u}) where
  toRationalMap : X.toScheme ⤏ Y.toScheme
  dominant : toRationalMap.IsDominant

end IntegralDominantRationalScheme
end AlgebraicGeometry
end
