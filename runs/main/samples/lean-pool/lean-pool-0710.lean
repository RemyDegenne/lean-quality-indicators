@[expose] public section

namespace LeanPool.Monsky

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "Triangle" => Fin 3 → ℝ²

local notation "Segment" => Fin 2 → ℝ²

open BigOperators

open Finset

lemma zig_cover_area {n : ℕ} :
    ∀ {Δ : Triangle}, Δ ∈ zigPartCover n → triangleArea Δ = 1 / (2 * n) := by
  intro Δ hΔ
  simp only [zigPartCover, one_div, mem_image, mem_univ, true_and] at hΔ
  have ⟨s,hs⟩ := hΔ
  rw [←hs, translateTriangle_area, scaleTriangle_area, areaΔ₀]
  simp

end LeanPool.Monsky
end
