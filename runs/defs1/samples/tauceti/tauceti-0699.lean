public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

/-- The source-to-sink orientation of the Bourbaki-numbered `A₂` graph. -/
abbrev preprojectiveA2Quiver := OrientedQuiver zigzagA2Graph
  (Orientation.ofLinearOrder zigzagA2Graph)

end TauCeti
end
