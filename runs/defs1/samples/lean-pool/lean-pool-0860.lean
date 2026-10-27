namespace IsoGraph

namespace Canon

/-- Start position of the first non-singleton cell, if any.  This is the target cell for
individualisation; picking the *first* one is an isomorphism-invariant rule. -/
def Part.targetCell (p : Part) (n : Nat) : Option Nat := cenTargetFrom p.cen n n 0

end Canon
end IsoGraph
