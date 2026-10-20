public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

section ValuationDomain

variable [IsDomain R] [ValuationRing R]

@[simp]
theorem restrictedResidue_add (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (f g : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    restrictedResidue a ham (f + g) = restrictedResidue a ham f + restrictedResidue a ham g := by
  simpa only [restrictedResidueHom_apply] using (map_add (restrictedResidueHom a ham) f g)

end ValuationDomain
end MvPowerSeries
end
