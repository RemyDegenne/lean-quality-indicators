public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

section LocalRing

variable [IsLocalRing R]

/-- Polynomial residue of a principal-adically restricted series at the maximal
ideal. No separatedness, completeness or nonzero-parameter assumption is needed. -/
noncomputable def restrictedResidueHom (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R) :
    adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) →+*
      MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R) :=
  reductionAtLargerIdeal (Ideal.span {a}) (IsLocalRing.maximalIdeal R)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ham))

end LocalRing
end MvPowerSeries
end
