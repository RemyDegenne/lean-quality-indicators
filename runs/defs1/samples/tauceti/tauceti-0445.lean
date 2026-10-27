public section

noncomputable section

open MeasureTheory

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A mild solution of `u' = A u`, `u(0) = x`, on `[0, ∞)`.  The integral is pointwise
Bochner integration in `X`.  Requiring the integral to lie in the domain makes the expression
`A (∫ s in (0, t], u s)` meaningful for an unbounded operator.

The predicate requires `X` to be complete, so the integral is not the default zero value
assigned by Bochner integration on incomplete spaces. -/
def IsMildSolution (A : X →ₗ.[ℝ] X) (x : X) (u : ℝ → X) : Prop :=
  CompleteSpace X ∧ ContinuousOn u (Set.Ici 0) ∧ u 0 = x ∧
    ∀ t : ℝ, 0 ≤ t → ∃ hut : (∫ s in Set.Ioc 0 t, u s) ∈ A.domain,
      A ⟨∫ s in Set.Ioc 0 t, u s, hut⟩ = u t - x

end TauCeti.Semigroups
end
end
