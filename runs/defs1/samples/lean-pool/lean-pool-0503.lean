namespace IsoGraph

namespace Canon

/-- Hash of the sequence of cell sizes.  Isomorphism-invariant. -/
def Part.shapeHash (p : Part) (n : Nat) : UInt64 := cenHashFrom p.cen n n 0 hashSeed

end Canon
end IsoGraph
