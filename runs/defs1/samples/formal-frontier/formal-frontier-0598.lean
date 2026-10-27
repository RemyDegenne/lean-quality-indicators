public section

set_option warningAsError true

open CategoryTheory Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

open PrimeIdealSpectrum

/-- A spectral space is homeomorphic to the prime spectrum of its compact-open lattice;
Fujiwara--Kato, *Foundations of Rigid Geometry I*, Theorem 2.2.8(2). -/
noncomputable def spaceSpectrumHomeomorph (X : SpectralCat) :
    X ≃ₜ PrimeIdealSpectrum (TopologicalSpace.CompactOpens X) :=
  (spaceSpectrumEquiv X).toHomeomorphOfContinuousOpen
    (continuous_spaceToSpectrum X) (isOpenMap_spaceToSpectrum X)

end SpectralStoneDuality
end
