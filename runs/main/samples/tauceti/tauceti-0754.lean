public section

namespace TauCeti.ValuationSpectrum

open TauCeti TauCeti.Huber TauCeti.Huber.PairOfDefinition Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A]

theorem spaAnalytic_subset_spa (Aplus : Subring A) :
    spaAnalytic Aplus ⊆ spa Aplus :=
  Set.inter_subset_left

end TauCeti.ValuationSpectrum
end
