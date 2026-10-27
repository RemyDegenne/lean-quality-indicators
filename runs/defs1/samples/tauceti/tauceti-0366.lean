public section

namespace TauCeti

open Metric

open scoped EuclideanSpace

/-- The unit circle `S¹ ⊆ ℝ²`. -/
abbrev Sphere1 : Type := sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

end TauCeti
end
