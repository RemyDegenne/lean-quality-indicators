@[expose] public section

open Homogenization Filter Topology

open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance

/-- The material derivative represented by the spacetime Fréchet derivative. -/
def materialDerivative (T : ℝ → Vec 2 → ℝ) (b : ℝ → Vec 2 → Vec 2) :
    ℝ → Vec 2 → ℝ := fun t x =>
  fderiv ℝ (Function.uncurry T) (t, x) (1, b t x)

end AVenhance.Infra.Section5
end
end
