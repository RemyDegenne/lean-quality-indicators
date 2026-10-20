public section

set_option warningAsError true

namespace MonomialOrder

open MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

theorem restrictedLeadingTerm_mem_ideal (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (J : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a})))
    {z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})} (hz : z ∈ J) :
    μ.restrictedLeadingTerm a ham z ∈ μ.restrictedLeadingTermIdeal a ham J :=
  Ideal.subset_span ⟨z, hz, rfl⟩

end MonomialOrder
end
