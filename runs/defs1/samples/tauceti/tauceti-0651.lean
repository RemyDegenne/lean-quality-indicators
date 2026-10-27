public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The pairing of a grid state against the `O`-markings of a grid diagram. -/
def JO (x : GridState n) : ℚ :=
  GridPoint.JCenter x.pointSet G.OSet

end GridDiagram
end TauCeti
end
