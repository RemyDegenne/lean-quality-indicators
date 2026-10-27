public section

namespace TauCeti

universe u v w

/-- A ring is **basic** when its quotient by the Jacobson radical is a finite product of division
rings, stated as that quotient being semisimple and reduced; the two readings agree by
`TauCeti.isBasic_iff_pi_divisionRing`.  When the quotient is semisimple anyway, as for a
finite-dimensional algebra over a field, the condition is reducedness alone -- every Wedderburn
block has size one -- which is `TauCeti.isBasic_iff_isReduced`. -/
def IsBasic (A : Type v) [Ring A] : Prop :=
  IsSemisimpleRing (A ⧸ Ring.jacobson A) ∧ IsReduced (A ⧸ Ring.jacobson A)

end TauCeti
end
