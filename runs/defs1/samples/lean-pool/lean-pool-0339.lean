@[expose] public section

open Metric Set

namespace Schoenflies

variable {Ω : Set Plane} {x y z : Plane}

/-- The carrier of a polygonal path: the union of the segments joining consecutive vertices.
A single vertex carries itself, so that a path may be constant. -/
def poly : List Plane → Set Plane
  | [] => ∅
  | [v] => {v}
  | u :: v :: rest => segment ℝ u v ∪ poly (v :: rest)

end Schoenflies
end
