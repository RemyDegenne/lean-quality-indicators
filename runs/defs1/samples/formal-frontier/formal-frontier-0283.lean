public section

set_option warningAsError true

open CategoryTheory Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

open PrimeIdealSpectrum

/-- The sober generic point associated to a prime ideal of compact opens. -/
noncomputable def spectrumToSpace (X : SpectralCat)
    (P : PrimeIdealSpectrum (TopologicalSpace.CompactOpens X)) : X :=
  (primeClosedSet_isIrreducible X P).genericPoint

end SpectralStoneDuality
end
