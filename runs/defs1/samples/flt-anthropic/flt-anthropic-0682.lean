namespace P2MW.S_WeierstrassCurve_finite_rationalHomSet_units

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

namespace RationalHomUnits

p2m_open

p2m_open

section OverK

variable {k : Type*} [Field k]

section Aff

variable [IsAlgClosed k] [DecidableEq k] (E : Affine k) [E.IsElliptic]

def affSet (q : kˣ × k × k × k) : Set (E.Point →+ E.Point) :=
  {u | ∃ B : Set k, B.Finite ∧ ∀ (x y : k) (h : E.Nonsingular x y), x ∉ B →
    ∃ h', u (.some x y h) =
      .some ((q.1 : k) ^ 2 * x + q.2.1) ((q.1 : k) ^ 3 * y + q.2.2.1 * x + q.2.2.2) h'}

end Aff
end OverK
end RationalHomUnits
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_finite_rationalHomSet_units
