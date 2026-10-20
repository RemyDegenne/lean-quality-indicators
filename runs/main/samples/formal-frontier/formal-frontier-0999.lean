public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

theorem restrictedContentFactor_spec (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) =
      Ideal.span {coeff (restrictedContentIndex a z) (z : MvPowerSeries σ R)} ∧
    (z : MvPowerSeries σ R) =
      C (coeff (restrictedContentIndex a z) (z : MvPowerSeries σ R)) *
        (restrictedContentFactor a z : MvPowerSeries σ R) ∧
    coeff (restrictedContentIndex a z)
      (restrictedContentFactor a z : MvPowerSeries σ R) = 1 := by
  simpa only [restrictedContentIndex, restrictedContentFactor] using
    Classical.choose_spec (Classical.choose_spec (exists_restricted_content_factor a z))

end MvPowerSeries
end
