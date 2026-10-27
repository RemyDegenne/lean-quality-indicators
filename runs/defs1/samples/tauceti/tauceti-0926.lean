public section

namespace TauCeti

namespace DominantWeight

variable {n : ℕ}

/-- The Young diagram of the **polynomial part** `λ - λₙ` of a dominant weight: its `i`-th row has
length `λᵢ - λₙ`.  Together with `TauCeti.DominantWeight.detShift` it presents `λ` as a
determinant twist of a polynomial weight. -/
def detShiftShape (l : DominantWeight n) : YoungDiagram := (l.shift (-l.detShift)).shape

end DominantWeight
end TauCeti
end
