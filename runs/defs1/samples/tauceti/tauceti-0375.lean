public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} (P : PlumbingGraph V)

/-- The subtype of characteristic covectors of the plumbing lattice. -/
abbrev characteristicVectors :=
  { k : V → ℤ // P.IsCharacteristicVector k }

end PlumbingGraph
end TauCeti
end
