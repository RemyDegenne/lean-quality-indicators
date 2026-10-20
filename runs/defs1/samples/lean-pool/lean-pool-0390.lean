universe u

open scoped NatOrdinal HahnSeries

open Berarducci HahnSeries MvPolynomial OrdinalGraded

public noncomputable section

namespace ConwayRefinement.Standalone.PrincipalRVAlgebraicIndependence

variable {K : Type u} [Field K]

variable {ι : Type} (deg : ι → NatOrdinal) (b : ι → nonpos K)
  (hB : IsMinimalHomogeneousFamily deg b)

include hB

/-- The lifts of the classes: the series themselves. -/
def lifts : Lifts deg (classes deg b hB) where
  lift i := toSeries (b i)
  represents i := represents_iff.mpr ⟨ordinalValue_toSeries_lt deg b hB i, rfl⟩

end ConwayRefinement.Standalone.PrincipalRVAlgebraicIndependence
end
