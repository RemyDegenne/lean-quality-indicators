@[expose] public section

namespace FD1D

noncomputable section

/-- Nodes of the complete dyadic tree at depth `d`. -/
abbrev DyadicNode (d : ℕ) := Fin (2 ^ d)

end
end FD1D
end
