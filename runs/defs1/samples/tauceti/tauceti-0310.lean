public section

namespace TauCeti.Sturm

open Polynomial List

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A alternating chain has opposite neighbors at every interior zero and
no real zero in its last entry. These are the properties of a signed remainder
chain after its common polynomial factor has been removed. -/
structure IsAlternating (cs : List (Polynomial R)) : Prop where
  /-- Every entry is a nonzero polynomial. -/
  nonzero : ∀ q ∈ cs, q ≠ 0
  /-- The terminal polynomial has no root in the coefficient ring. -/
  last : ∀ q, cs.getLast? = some q → ∀ r, q.eval r ≠ 0
  /-- At an interior zero the adjacent values are nonzero and have opposite signs. -/
  alternate : ∀ (i : ℕ) (q0 q1 q2 : Polynomial R), cs[i]? = some q0 →
    cs[i + 1]? = some q1 → cs[i + 2]? = some q2 → ∀ r, q1.eval r = 0 →
    q0.eval r * q2.eval r < 0

end OrderedRing
end TauCeti.Sturm
end
