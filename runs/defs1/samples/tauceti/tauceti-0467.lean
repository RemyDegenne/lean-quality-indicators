public section

namespace TauCeti

namespace GridRectangleHexagonDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Apply a rectangle and a commutation hexagon in the opposite order when their vertical
side pairs are disjoint. -/
def commute (D : GridRectangleHexagonDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    GridHexagonRectangleDecomposition a s s' x z where
  middle := (D.toRectangleDecomposition.commute h).middle
  first := GridCommutationHexagonBetween.ofToGridRectangleEq
    (D.toRectangleDecomposition.commute h).first D.second
    (D.toRectangleDecomposition.commute_first_toGridRectangle h)
  second := (D.toRectangleDecomposition.commute h).second

end GridRectangleHexagonDecomposition
end TauCeti
end
