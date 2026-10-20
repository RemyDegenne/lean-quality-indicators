@[expose] public section

namespace AleksandrovDifferentiability

open Asymptotics

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HasSubgradientLinearizationOnAt

theorem of_eventually_mem_closure_convexHull_image
    {ι : Type*} {domain approach : Set E} {u : E → ℝ} {x p₀ : E}
    {B : E →L[ℝ] E} {t : E → Set ι} {g : E → ι → E}
    (hslopes : ∀ ε > 0, ∀ᶠ y in 𝓝[approach] x,
      ∀ q ∈ t y, ‖g y q - (p₀ + B (y - x))‖ ≤ ε * ‖y - x‖)
    (hsubgradients : ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        p ∈ closure (convexHull ℝ ((g y) '' t y))) :
    HasSubgradientLinearizationOnAt domain approach u x p₀ B := by
  intro ε hε
  filter_upwards [hslopes ε hε, hsubgradients] with y hslopes_y hsubgradients_y p hp
  exact
    norm_sub_le_of_mem_closure_convexHull_image_norm_sub_le
      (a := p₀ + B (y - x)) (p := p) (R := ε * ‖y - x‖)
      hslopes_y (hsubgradients_y p hp)

end HasSubgradientLinearizationOnAt
end AleksandrovDifferentiability
end
