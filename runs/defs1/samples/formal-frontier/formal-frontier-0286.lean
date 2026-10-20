public section

set_option warningAsError true

open Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

variable {A : Type u} [DistribLattice A] [BoundedOrder A]

namespace PrimeIdealSpectrum

/-- Prime ideals with their Zariski topology are the points of the ideal frame. -/
def pointHomeomorph : PrimeIdealSpectrum A ≃ₜ Locale.PT (Order.Ideal A) :=
  pointEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

end PrimeIdealSpectrum
end SpectralStoneDuality
end
