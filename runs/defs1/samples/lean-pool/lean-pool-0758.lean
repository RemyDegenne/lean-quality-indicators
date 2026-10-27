@[expose] public section

namespace FD1D

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

open Set MeasureTheory

/--
An exact finite supply configuration: `m` labeled real points, each in the
unit interval and carrying a certified depth-`L` leaf label.
-/
structure SupplyConfiguration (L m : ℕ) where
  /-- Spatial coordinate of each item in the supply configuration. -/
  location : Fin m → ℝ
  /-- Dyadic cell containing each item in the supply configuration. -/
  leaf : Fin m → DyadicNode L
  location_mem_unit : ∀ j, location j ∈ Icc (0 : ℝ) 1
  location_mem_cell : ∀ j, location j ∈ dyadicCell (leaf j)

end
end FD1D
end
