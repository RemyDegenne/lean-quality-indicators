public section

namespace TauCeti

variable (G : Type*) [CommGroup G]

/-- **The maximal elementary-2 quotient `G / G²`** of a commutative group, written additively on
`Additive G`. -/
abbrev ElementaryTwoQuotient : Type _ :=
  ModN (Additive G) 2

end TauCeti
end
