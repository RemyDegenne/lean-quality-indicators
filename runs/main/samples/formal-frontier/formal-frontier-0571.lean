public section

set_option warningAsError true

open Order Set TopologicalSpace Topology

universe u v w

namespace SpectralStoneDuality

variable {A : Type u} [DistribLattice A] [BoundedOrder A]

namespace PrimeIdealSpectrum

@[simp]
theorem compactOpenOrderIso_apply (a : A) :
    compactOpenOrderIso (A := A) a = principalCompactOpen a := rfl

end PrimeIdealSpectrum
end SpectralStoneDuality
end
