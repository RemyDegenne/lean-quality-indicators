@[expose] public section

namespace LeanPool.Monsky

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "Triangle" => Fin 3 → ℝ²

local notation "Segment" => Fin 2 → ℝ²

open BigOperators

open Finset

/-- `isDisjointCover X S` states that `S` covers `X` and its open hulls are pairwise disjoint. -/
def isDisjointCover {n : ℕ} (X : Set ℝ²) (S : Set (Fin n → ℝ²)) : Prop :=
  isCover X S ∧ isDisjointPolygonSet S

end LeanPool.Monsky
end
