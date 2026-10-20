public section

set_option warningAsError true

open CategoryTheory Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

open PrimeIdealSpectrum

/-- The spectral-space-side component of Stone duality. -/
noncomputable def spaceUnitComponent (X : SpectralCat) :
    X ≅ (compactOpenFunctor ⋙ spectrumFunctor).obj X :=
  SpectralCat.isoMk (spaceSpectrumHomeomorph X)

end SpectralStoneDuality
end
