public section

set_option warningAsError true

open CategoryTheory Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

attribute [instance] SpectralCat.topology SpectralCat.spectral

namespace SpectralCat

/-- Bundle a spectral space. -/
abbrev of (X : Type u) [TopologicalSpace X] [SpectralSpace X] : SpectralCat where
  carrier := X

end SpectralCat
end SpectralStoneDuality
end
