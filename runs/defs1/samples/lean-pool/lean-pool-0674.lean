@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem.Contracts

open AVenhance AVenhance.Infra.FullTheorem

/-- The exponent of `R^{-p}`: `p = q/(1+γ/2) · e`. -/
def unifP (β : ℝ) : ℝ := q β / (1 + gamma β / 2) * unifE β

end AVenhance.Infra.FullTheorem.Contracts
end
end
