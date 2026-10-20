@[expose] public section

namespace LeanPool.Monsky

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "Triangle" => Fin 3 → ℝ²

local notation "Segment" => Fin 2 → ℝ²

open BigOperators

open Finset

lemma boundary_in_square_boundary {x : ℝ²} (hx : x ∈ boundary unitSquare) :
    ∃ i, x ∈ closedHull (squareBoundaryBig i) := by
  rw [boundary_unitSquare_eq] at hx
  have ⟨j, hj⟩ := hx.2
  fin_cases j <;> obtain hj | hj := hj
  · exact ⟨3, by simp_all [squareBoundaryBig_eq]⟩
  · exact ⟨1, by simp_all [squareBoundaryBig_eq]⟩
  · exact ⟨0, by simp_all [squareBoundaryBig_eq]⟩
  · exact ⟨2, by simp_all [squareBoundaryBig_eq]⟩

end LeanPool.Monsky
end
