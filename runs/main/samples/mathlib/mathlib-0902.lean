public section

open Filter Finset Set

open scoped Topology ContDiff

namespace Real

variable {x : ℝ}

theorem differentiableOn_log : DifferentiableOn ℝ log {0}ᶜ := fun _x hx =>
  (differentiableAt_log hx).differentiableWithinAt

end Real
end
