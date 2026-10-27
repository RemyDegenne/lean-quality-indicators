@[expose] public section

namespace MooreBound

open Set

namespace DegreeDiameter

open SimpleGraph

universe u

/-- Recover the encoded neighboring edge. -/
def edgeOfLineGraphNeighborCode {V : Type u} {G : SimpleGraph V} {e : G.edgeSet}
    (c : Σ v : {v : V // v ∈ e.1}, G.neighborSet v.1) : G.edgeSet :=
  ⟨s(c.1.1, c.2.1), G.mem_edgeSet.mpr c.2.2⟩

end DegreeDiameter
end MooreBound
end
