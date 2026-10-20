@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Integral scheme equipped with an arbitrary chosen total structure morphism. -/
structure IntegralDominantRationalSchemeOver (S : Scheme.{u}) where
  toScheme : Scheme.{u}
  toBase : toScheme ⟶ S
  integral : IsIntegral toScheme

end AlgebraicGeometry
end
