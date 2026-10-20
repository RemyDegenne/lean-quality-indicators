public section

set_option warningAsError true

open Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

variable {A : Type u} [DistribLattice A] [BoundedOrder A]

namespace PrimeIdealSpectrum

theorem ofPoint_toPoint (P : PrimeIdealSpectrum A) : ofPoint (toPoint P) = P := by
  apply Subtype.ext
  apply Order.Ideal.ext
  ext a
  change ¬ (¬ Order.Ideal.principal a ≤ P.1) ↔ a ∈ P.1
  rw [not_not, Order.Ideal.principal_le_iff]

end PrimeIdealSpectrum
end SpectralStoneDuality
end
