public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

namespace TauCeti

namespace RealProjectiveSpace

variable {n : ℕ}

variable (n) in
/-- The point of the upper hemisphere of `Sᵏ ⊆ Sⁿ` lying over `v ∈ ℝᵏ`: its first `k`
coordinates are those of `v`, its coordinate `k` is `√(1 - ‖v‖²)`, and the remaining ones vanish.
For `k ≤ n` and `‖v‖ ≤ 1` it lies on the unit sphere (`norm_hemispherePoint`). This is the
coordinate form, for `p = eₖ` and composed with the inclusion `Sᵏ ⊆ Sⁿ`, of the lift
`y ↦ y + √(1 - ‖y‖²) • p` inverting `TauCeti.hemisphereHomeomorph`. -/
def hemispherePoint {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 fun j =>
    if h : (j : ℕ) < k then v ⟨j, h⟩ else if (j : ℕ) = k then √(1 - ‖v‖ ^ 2) else 0

end RealProjectiveSpace
end TauCeti
end
end
