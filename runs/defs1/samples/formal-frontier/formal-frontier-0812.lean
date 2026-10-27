public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

/-- The restricted factor normalized at `restrictedContentIndex`. -/
noncomputable def restrictedContentFactor (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) :=
  Classical.choose (Classical.choose_spec (exists_restricted_content_factor a z))

end MvPowerSeries
end
