@[expose] public section

namespace LeanPool.Monsky

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "Triangle" => Fin 3 → ℝ²

local notation "Segment" => Fin 2 → ℝ²

open BigOperators

open Finset

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]

variable (v : Valuation ℝ Γ₀)

lemma valuation_max
  {A a₁ a₂ a₃ a₄ a₅ : ℝ}
  (h1 : v (A) > v (a₁))
  (h2 : v (A) > v (a₂))
  (h3 : v (A) > v (a₃))
  (h4 : v (A) > v (a₄))
  (h5 : v (A) > v (a₅)) :
  v (A + a₁ + a₂ + a₃ + a₄ + a₅) = v (A) := by
  -- move brackets to the right
  repeat rw [add_assoc]
  -- Now just write the function representing the proof term directly.
  -- exact map_add_eq_of_lt_left v <| map_add_lt v h1 <| map_add_lt v h2 h3
  apply Valuation.map_add_eq_of_lt_left
  repeat (
    apply Valuation.map_add_lt v _ _
    assumption
  )
  assumption

end LeanPool.Monsky
end
