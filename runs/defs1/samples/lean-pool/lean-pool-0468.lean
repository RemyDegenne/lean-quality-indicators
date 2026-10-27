@[expose] public section

namespace LeanPool.Monsky

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "Triangle" => Fin 3 → ℝ²

local notation "Segment" => Fin 2 → ℝ²

open BigOperators

open Finset

open MeasureTheory

/-- The unit triangle with vertices `(0,0)`, `(1,0)` and `(0,1)`. -/
def unitTriangle : Triangle := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)

end LeanPool.Monsky
end
