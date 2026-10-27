public section

namespace TauCeti.Sporadic.BabyMonster

/-- The nodes joined to a given node by an edge, read off the Coxeter matrix rather than off the
edge list, so that a comparison with the diagram sees the matrix that the relators are built
from. -/
def neighbors (i : Fin 11) : List (Fin 11) :=
  (List.finRange 11).filter fun j => coxeterMatrix i j = 3

end TauCeti.Sporadic.BabyMonster
end
