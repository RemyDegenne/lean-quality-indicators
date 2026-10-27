@[expose] public section

namespace LeanPool.Monsky

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "Triangle" => Fin 3 → ℝ²

local notation "Segment" => Fin 2 → ℝ²

open BigOperators

open Finset

open MeasureTheory

/-- Translation by the first endpoint of a segment. -/
def segmentTranslation (L : Segment) := translation (L 0)

end LeanPool.Monsky
end
