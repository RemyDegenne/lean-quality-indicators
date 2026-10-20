public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

namespace FiniteLocallyFreeSheaf

/-- The full category of finite locally free sheaves of rank `r` at every point of `X`. -/
abbrev FixedRank (X : Scheme.{u}) (r : ℕ) : Type _ :=
  (isConstantRank X r).FullSubcategory

end FiniteLocallyFreeSheaf
end
end AlgebraicGeometry
end TauCeti
end
