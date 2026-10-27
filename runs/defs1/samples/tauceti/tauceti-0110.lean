public section

namespace TauCeti.OrientedPDCode

open PDCode

/-- Adjoin a cancelling clasp between two additional oriented circles in a disc disjoint
from `D`. Compare it with `(D.adjoinCircle o₁).adjoinCircle o₂`. -/
def adjoinTwoCircleClasp {n : ℕ} (D : OrientedPDCode n) (o₁ o₂ b : Bool) : OrientedPDCode (n + 2) :=
  D.disjointUnion (twoCircleClasp o₁ o₂ b)

end TauCeti.OrientedPDCode
end
