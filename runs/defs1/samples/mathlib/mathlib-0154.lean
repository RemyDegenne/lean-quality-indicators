@[expose] public section

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v}

variable (G : SimpleGraph V) (G' : SimpleGraph V')

namespace Path

variable {G G'}

/-- The reverse of a path is another path.  See also `SimpleGraph.Walk.reverse`. -/
@[symm, simps]
def reverse {u v : V} (p : G.Path u v) : G.Path v u :=
  ⟨Walk.reverse p, p.property.reverse⟩

end Path
end SimpleGraph
end
