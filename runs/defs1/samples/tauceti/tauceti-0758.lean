public section

namespace TauCeti

open _root_.Complex

namespace PoincareDisc

/-- The standard disc automorphism with rotation `u` and center `a` as an isometric
equivalence of the Poincaré disc. -/
noncomputable def unitDiscStandardAutomorphismIsometryEquiv
    (u : Circle) (a : Complex.UnitDisc) : PoincareDisc ≃ᵢ PoincareDisc :=
  isometryEquivOfHyperbolicDistEq (unitDiscStandardAutomorphismEquiv u a)
    (hyperbolicDist_unitDiscStandardAutomorphismEquiv u a)

end PoincareDisc
end TauCeti
end
