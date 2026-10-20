@[expose] public section

namespace AleksandrovDifferentiability

open Asymptotics

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem convex_setOf_subgradientOn
    {s : Set E} {u : E → ℝ} {x : E} :
    Convex ℝ {p : E | SubgradientOn s u x p} := by
  intro p₀ hp₀ p₁ hp₁ a b ha hb hab
  exact hp₀.smul_add_smul hp₁ ha hb hab

end AleksandrovDifferentiability
end
